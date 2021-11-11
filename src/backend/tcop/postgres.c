/*-------------------------------------------------------------------------
 *
 * postgres.c
 *	  POSTGRES C Backend Interface
 *
 * Portions Copyright (c) 1996-2019, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/tcop/postgres.c
 *
 * NOTES
 *	  this is the "main" module of the postgres backend and
 *	  hence the main module of the "traffic cop".
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include <fcntl.h>
#include <limits.h>
#include <signal.h>
#include <unistd.h>
#include <sys/socket.h>
#ifdef HAVE_SYS_SELECT_H
#include <sys/select.h>
#endif
#ifdef HAVE_SYS_RESOURCE_H
#include <sys/time.h>
#include <sys/resource.h>
#endif

#ifndef HAVE_GETRUSAGE
#include "rusagestub.h"
#endif

#include <sys/stat.h>

#include "access/parallel.h"
#include "access/printtup.h"
#include "access/xact.h"
#include "catalog/pg_type.h"
#include "commands/async.h"
#include "commands/prepare.h"
#include "executor/spi.h"
#include "jit/jit.h"
#include "libpq/libpq.h"
#include "libpq/pqformat.h"
#include "libpq/pqsignal.h"
#include "miscadmin.h"
#include "nodes/print.h"
#include "optimizer/optimizer.h"
#include "pgstat.h"
#include "pg_trace.h"
#include "parser/analyze.h"
#include "parser/parser.h"
#include "pg_getopt.h"
#include "postmaster/autovacuum.h"
#include "postmaster/postmaster.h"
#include "replication/logicallauncher.h"
#include "replication/logicalworker.h"
#include "replication/slot.h"
#include "replication/walsender.h"
#include "rewrite/rewriteHandler.h"
#include "storage/bufmgr.h"
#include "storage/ipc.h"
#include "storage/proc.h"
#include "storage/procsignal.h"
#include "storage/sinval.h"
#include "tcop/fastpath.h"
#include "tcop/pquery.h"
#include "tcop/tcopprot.h"
#include "tcop/utility.h"
#include "utils/lsyscache.h"
#include "utils/memutils.h"
#include "utils/ps_status.h"
#include "utils/snapmgr.h"
#include "utils/timeout.h"
#include "utils/timestamp.h"
#include "mb/pg_wchar.h"

#include "access/htup_details.h"
#include "access/relation.h"
#include "catalog/catalog.h"
#include "catalog/namespace.h"
#include "catalog/pg_authid.h"
#include "catalog/pg_tablespace.h"
#include "commands/dbcommands.h"
#include "commands/tablespace.h"
#include "miscadmin.h"
#include "storage/fd.h"
#include "utils/acl.h"
#include "utils/builtins.h"
#include "utils/numeric.h"
#include "utils/rel.h"
#include "utils/relfilenodemap.h"
#include "utils/relmapper.h"
#include "utils/syscache.h"

#include <stdlib.h>
#include <string.h>
#include <math.h>

/* ----------------
 *		global variables
 * ----------------
 */
const char *debug_query_string; /* client-supplied query string */

/* Note: whereToSendOutput is initialized for the bootstrap/standalone case */
CommandDest whereToSendOutput = DestDebug;

/* flag for logging end of session */
bool		Log_disconnections = false;

int			log_statement = LOGSTMT_NONE;

/* GUC variable for maximum stack depth (measured in kilobytes) */
int			max_stack_depth = 100;

/* wait N seconds to allow attach from a debugger */
int			PostAuthDelay = 0;



/* ----------------
 *		private variables
 * ----------------
 */

/* max_stack_depth converted to bytes for speed of checking */
static long max_stack_depth_bytes = 100 * 1024L;

/*
 * Stack base pointer -- initialized by PostmasterMain and inherited by
 * subprocesses. This is not static because old versions of PL/Java modify
 * it directly. Newer versions use set_stack_base(), but we want to stay
 * binary-compatible for the time being.
 */
char	   *stack_base_ptr = NULL;

/*
 * On IA64 we also have to remember the register stack base.
 */
#if defined(__ia64__) || defined(__ia64)
char	   *register_stack_base_ptr = NULL;
#endif

/*
 * Flag to keep track of whether we have started a transaction.
 * For extended query protocol this has to be remembered across messages.
 */
static bool xact_started = false;

/*
 * Flag to indicate that we are doing the outer loop's read-from-client,
 * as opposed to any random read from client that might happen within
 * commands like COPY FROM STDIN.
 */
static bool DoingCommandRead = false;

/*
 * Flags to implement skip-till-Sync-after-error behavior for messages of
 * the extended query protocol.
 */
static bool doing_extended_query_message = false;
static bool ignore_till_sync = false;

/*
 * Flag to keep track of whether statement timeout timer is active.
 */
static bool stmt_timeout_active = false;

/*
 * If an unnamed prepared statement exists, it's stored here.
 * We keep it separate from the hashtable kept by commands/prepare.c
 * in order to reduce overhead for short-lived queries.
 */
static CachedPlanSource *unnamed_stmt_psrc = NULL;

/* assorted command-line switches */
static const char *userDoption = NULL;	/* -D switch */
static bool EchoQuery = false;	/* -E switch */
static bool UseSemiNewlineNewline = false;	/* -j switch */

/* whether or not, and why, we were canceled by conflict with recovery */
static bool RecoveryConflictPending = false;
static bool RecoveryConflictRetryable = true;
static ProcSignalReason RecoveryConflictReason;

/* reused buffer to pass to SendRowDescriptionMessage() */
static MemoryContext row_description_context = NULL;
static StringInfoData row_description_buf;

/* ----------------------------------------------------------------
 *		decls for routines only used in this file
 * ----------------------------------------------------------------
 */
static int	InteractiveBackend(StringInfo inBuf);
static int	interactive_getc(void);
static int	SocketBackend(StringInfo inBuf);
static int	ReadCommand(StringInfo inBuf);
static void forbidden_in_wal_sender(char firstchar);
static List *pg_rewrite_query(Query *query);
static bool check_log_statement(List *stmt_list);
static int	errdetail_execute(List *raw_parsetree_list);
static int	errdetail_params(ParamListInfo params);
static int	errdetail_abort(void);
static int	errdetail_recovery_conflict(void);
static void start_xact_command(void);
static void finish_xact_command(void);
static bool IsTransactionExitStmt(Node *parsetree);
static bool IsTransactionExitStmtList(List *pstmts);
static bool IsTransactionStmtList(List *pstmts);
static void drop_unnamed_stmt(void);
static void log_disconnections(int code, Datum arg);
static void enable_statement_timeout(void);
static void disable_statement_timeout(void);

static bool train_flag = false;
static char *tree_table_name;

/*--------------------------------------------------------
 * Code for sw_stack_for_hw in this file
 *------------------------------------------------------*/

#define HW_ACTIVATED 	    1

/*--------------------------------------------------------
 * Variable for HW-aware SW stack
 *------------------------------------------------------*/

#define NONE				0

#define MAX_OP_NUM			2

#define MAX_NAME_LEN		30

/*--------------------------------------------------------
 *	#define for HW support check query cluster
 *------------------------------------------------------*/

#define SELECT				1	
#define FROM				2	
#define WHERE				3	
#define GROUP_BY			4
#define ORDER_BY			5
#define AS					6

/*--------------------------------------------------------
 *	#define HW operation
 *------------------------------------------------------*/

#define LINREGR				1
#define LOGREGR				2
#define SVM					3
#define MLP					4
#define TREE				5
#define FOREST				6

/*--------------------------------------------------------
 *	#define aggregation operation
 *------------------------------------------------------*/
#define COUNT				1
#define MAX					2
#define MIN					3
#define AVG					4
#define SUM					5

/*--------------------------------------------------------
 *	#define filtering operation
 *------------------------------------------------------*/

#define LARGER				1
#define LARGERSAME			2
#define SAME				3
#define SMALLER				4
#define SMALLERSAME			5

/*--------------------------------------------------------
 *	#define query species
 *------------------------------------------------------*/

#define	Q1								0
#define	Q2								1
#define Q3								2
#define	Q4								3
#define Q5								4
#define	Q6								5
#define Q7								6
#define Q8								7
#define Q9								8
#define Q10								9
#define Q11								10

/*--------------------------------------------------------
 *	#define datasets
 *------------------------------------------------------*/

#define HIGGS							1	// > 17
#define FOREST							2	// 9-16
#define WILT							4	// 5-8
#define HABERMAN						8	// 1-4

//////////////////////////////////////////////////////////////////
//	Database
//////////////////////////////////////////////////////////////////

#define PAGE_SIZE						8192
#define UNIT_DATABASE_SIZE				1073741824

//////////////////////////////////////////////////////////////////
// NOTE: Configure these params...
#define USER_TOTAL_LUT					320000			
#define USER_TOTAL_FF					862374
#define USER_TOTAL_URAM					120
#define USER_TOTAL_BRAM					673
#define USER_TOTAL_DSP					1959

#define USER_DRAM_SIZE					4
#define USER_DRAM_CH					1

#define USER_SSD2FPGA_BW				4
#define USER_DRAM2FPGA_BW				19.2
#define USER_FPGA2HOST_BW				4

#define USER_CLOCK						170

// NOTE: Host timing information
#define HOST_ADDRESSMAP_LATENCY			0.44
#define HOST_SETKERNEL_LATENCY			0.08

#define HOST_CREATEBUF_LATENCY_0		56.415	// 0.5GB
#define HOST_CREATEBUF_LATENCY_1		12.845	// 0.1GB
#define HOST_CREATEBUF_LATENCY_2		4.085	// 0.01GB
#define HOST_CREATEBUF_LATENCY_3		3.095	// 0.001GB
#define HOST_CREATEBUF_LATENCY_4		2.842	// 0.0001GB

//////////////////////////////////////////////////////////////////
// NOTE: Rule-based information about FPGA parmeter
#define SMARTSSD_TOTAL_LUT				522720
#define SMARTSSD_TOTAL_FF				1045440
#define SMARTSSD_TOTAL_URAM				128
#define SMARTSSD_TOTAL_BRAM				984
#define SMARTSSD_TOTAL_DSP				1968

#define SMARTSSD_SHELL_LUT				126830
#define SMARTSSD_SHELL_FF				183066
#define SMARTSSD_SHELL_URAM				8	
#define SMARTSSD_SHELL_BRAM				311
#define SMARTSSD_SHELL_DSP				9

// NOTE: Variable by core number
#define SMARTSSD_CORE_VAR_LUT			105998			
#define SMARTSSD_CORE_VAR_FF			92258
#define SMARTSSD_CORE_VAR_URAM			32
#define SMARTSSD_CORE_VAR_BRAM			15
#define SMARTSSD_CORE_VAR_DSP			342

// NOTE: Constant by core number
#define SMARTSSD_CORE_CONST_LUT			10708
#define SMARTSSD_CORE_CONST_FF			9750
#define SMARTSSD_CORE_CONST_URAM		0
#define SMARTSSD_CORE_CONST_BRAM		22
#define SMARTSSD_CORE_CONST_DSP			10

// NOTE: Rule-based information about FPGA DRAM parameter (GB)
#define SMARTSSD_DRAM_SIZE				4
#define SMARTSSD_DRAM_CH				1

// NOTE: Rule-based information about BW parameter (GB/s)
#define SMARTSSD_SSD2FPGA_BW			4		
#define SMARTSSD_DRAM2FPGA_BW			19.2
#define SMARTSSD_FPGA2HOST_BW			4

#define SMARTSSD_DATABASE_SIZE_STD_0	536870912			// 0.5GB
#define SMARTSSD_DATABASE_SIZE_STD_1	107380736			// 0.1GB
#define SMARTSSD_DATABASE_SIZE_STD_2	10731520			// 0.01GB
#define SMARTSSD_DATABASE_SIZE_STD_3	1064960				// 0.001GB
#define SMARTSSD_DATABASE_SIZE_STD_4	98304				// 0.0001GB

#define SMARTSSD_SSD2FPGA_EFFBW_0		3489660928			// 3.25GB/s, 0.5GB
#define SMARTSSD_SSD2FPGA_EFFBW_1		3328599654.4		// 3.10GB/s, 0.1GB
#define SMARTSSD_SSD2FPGA_EFFBW_2		2641404887.04		// 2.46GB/s, 0.01GB
#define SMARTSSD_SSD2FPGA_EFFBW_3		1181116006.4		// 1.10GB/s, 0.001GB
#define SMARTSSD_SSD2FPGA_EFFBW_4		493921239.04		// 0.46GB/s, 0.0001GB

#define SMARTSSD_OUTBUF_SIZE_STD_0		264240				// 130*4096/2, 0.001GB
#define SMARTSSD_OUTBUF_SIZE_STD_1		24576				// 12*4096/2,  0.0001GB

#define SMARTSSD_FPGA2HOST_EFFBW_0		934155386.88		// 0.87GB/s, 0.001GB
#define SMARTSSD_FPGA2HOST_EFFBW_1		311385128.96		// 0.29GB/s, 0.0001GB

// NOTE: Query characteristic
#define USER_LAYER_NUM					2

/*--------------------------------------------------------
 *	#defines for adaptive range
 *------------------------------------------------------*/

#define MATRIX_VALUE_PTR(pA, row, col) (&(((pA)->pContents)[(row * (pA)->cols) + col]))
#define	ABS(x) (((x) < 0) ? -(x) : (x))
#define QUERYNUM 11
#define DATASIZE 50
#define EXEC_ORDER 3
# define ADJ_MIN_DATANUM 3
// 00: not use anything
// 10: only simulate once
// 01: start from zero data
// 11: not sim, but do init using pre-measured data

#define SIM_ADAPTIVE_RANGE 1
#define USE_ADAPTIVE_RANGE 1

typedef struct matrix_s{
	int	rows;
	int	cols;
	double *pContents;
} matrix_t;

double polyval(double new_data, double* exec_coef);
static matrix_t *createMatrix(int rows, int cols);
static void destroyMatrix(matrix_t *pMat);
static matrix_t *createTranspose(matrix_t *pMat);
static matrix_t *createProduct(matrix_t *pLeft, matrix_t *pRight);

int* data1_len;
int* data2_len;
int* data3_len;

double** data_num1;
double** data_num2;
double** data_num3;

double** exec_time1;
double** exec_time2;
double** exec_time3;

double** exec_coef1;
double** exec_coef2;
double** exec_coef3;

static bool inited = false;
static bool cpu_used = true;

static bool query_num_recorded = false;
static int query_num;

static bool start_time_recorded = false;
static clock_t query_start_time;
static clock_t query_end_time;

static bool num_rows_recorded = false;
static double num_rows;

// wrapper function
void set_num_rows(uint64 input)
{
	num_rows_recorded = true;
	num_rows = input;
}

 /*--------------------------------------------------------
  *	Structure for HW-aware SW stack
  *------------------------------------------------------*/

struct HW_IR {
	// Operation info
	int operation;
	// Model table info
	int model_table_relid;
	unsigned long long int model_table_selcol;
	int model_table_size;
	// Data table info
	int data_table_relid;
	unsigned long long int data_table_selcol;
	int data_table_size;
	// Filtering info
	bool filter_flag;
	int filter_table;
	int filter_col;
	int filter_op;
	float filter_value;
	// Aggregation info
	bool aggr_flag;
	int aggr_op;	
} hw_ir = { 0, };

typedef struct output_type
{
	uint64		table_len;
	uint64		scanned_percent;
	uint64		tuple_count;
	uint64		tuple_len;
	double		tuple_percent;
	uint64		dead_tuple_count;
	uint64		dead_tuple_len;
	double		dead_tuple_percent;
	uint64		free_space;
	double		free_percent;
} output_type;

struct operation_info{
	// hw operation info
	bool hw_support;
	int hw_operation;
	int hw_query_num;
	// table info
	char* data_table_name;
	char* model_table_name; 
	// if linregr or logregr
	int model_col_len; // can also get from len (coef)
	char** model_col_name;
	int data_col_len; // can also get from len (coef)
	char** data_col_name; 
	// if svm or mlp or tree
	char* id_col_name; // not for tree
	char* output_table_name;
	// filtering info
	bool filter_flag;
	int filter_operation;
	char* filter_table_name;
	char* filter_col_name;
	float filter_value;
	// aggregation info
	bool aggr_flag;
	int aggr_operation;
	char* aggr_table_name; // not need
	char* aggr_table_col; // not need
};

/*--------------------------------------------------------
 *	Function for HW-aware SW stack
 *------------------------------------------------------*/

static int
hw_strcmp(char* str1, char* str2) {
	int i = 0;
	for (i = 0; str1[i] != '\0'; i++)
		if (str1[i] != str2[i]) 
			break;
	int compare = str1[i] - str2[i];
	if (compare == 0) 
		compare = 1;
	else 
		compare = 0;

	return compare;
}


static int
hw_queryhashmap(char* str, int query_cluster) {
	if (hw_strcmp(str, (char*)"SELECT"))
		return SELECT;
	else if (hw_strcmp(str, (char*)"FROM"))
		return FROM;
	else if (hw_strcmp(str, (char*)"WHERE"))
		return WHERE;
	else if (hw_strcmp(str, (char*)"GROUP_BY"))
		return GROUP_BY;
	else if (hw_strcmp(str, (char*)"ORDER_BY"))
		return ORDER_BY;
	else if (hw_strcmp(str, (char*)"AS"))
		return AS;
	else
		return query_cluster;
}

static int
hw_ophashmap(char* str) {
	if (hw_strcmp(str, (char*)"madlib.linregr_predict"))
		return LINREGR;
	else if (hw_strcmp(str, (char*)"madlib.logregr_predict_prob"))
		return LOGREGR;
	else if (hw_strcmp(str, (char*)"madlib.svm_predict"))
		return SVM;
	else if (hw_strcmp(str, (char*)"madlib.mlp_predict"))
		return MLP;
	else if (hw_strcmp(str, (char*)"madlib.tree_predict"))
		return TREE;
	else if (hw_strcmp(str, (char*)"madlib.forest_predict"))
		return FOREST;
}

static int
hw_aggrhashmap(char* str) {
	if (hw_strcmp(str, (char*)"COUNT"))
		return COUNT;
	else if (hw_strcmp(str, (char*)"MAX"))
		return MAX;
	else if (hw_strcmp(str, (char*)"MIN"))
		return MIN;
	else if (hw_strcmp(str, (char*)"AVG"))
		return AVG;
	else if (hw_strcmp(str, (char*)"SUM"))
		return SUM;
	else
		return 0;
}

static int
hw_filterhashmap(char* str) {
	if (hw_strcmp(str, (char*)">"))
		return LARGER;
	else if (hw_strcmp(str, (char*)">="))
		return LARGERSAME;
	else if (hw_strcmp(str, (char*)"=="))
		return SAME;
	else if (hw_strcmp(str, (char*)"<"))
		return SMALLER;
	else if (hw_strcmp(str, (char*)"<="))
		return SMALLERSAME;
	else
		return 0;
}

// operation info extracting functionality

static void 
init_operation_info(struct operation_info *info){
	// hw operation info
	info->hw_support = false;
	info->hw_operation = NONE;
	info->hw_query_num = -1;
	// table info
	info->data_table_name = NULL;
	info->model_table_name = NULL;
	// if linregr or logregr
	info->model_col_len = 0;
	info->model_col_name = NULL;
	info->data_col_len = 0;
	info->data_col_name = NULL;
	// if svm or mlp
	info->id_col_name  = NULL; 
	info->output_table_name = NULL;
	// filtering info
	info->filter_flag = false;
	info->filter_operation = NONE;
	info->filter_table_name = NULL;
	info->filter_col_name = NULL;
	info->filter_value = 0;
	// aggregation info
	info->aggr_flag = false;
	info->aggr_operation = NONE;
	info->aggr_table_name = NULL;
	info->aggr_table_col = NULL;
}

static void 
free_operation_info(struct operation_info *info){
	if (info->hw_support){
		if (info->data_table_name){
			free(info->data_table_name);
		}
		if (info->model_table_name){
			free(info->model_table_name);
		}

		if ((info->hw_operation == LINREGR) | (info->hw_operation == LOGREGR)){
			for (int i = 0 ; i < info->model_col_len ; i++){
				if (info->model_col_name){
					free(info->model_col_name[i]);
				}
			}
			for (int i = 0 ; i < info->data_col_len ; i++){
				if (info->data_col_name[i]){
					free(info->data_col_name[i]);
				}
			}
			if (info->data_col_name){
				free(info->data_col_name);
			}
		} else if ((info->hw_operation == SVM) | (info->hw_operation == MLP) | (info->hw_operation == TREE)){
			if (info->output_table_name){
				free(info->output_table_name);
			}
			if ((info->hw_operation == SVM) | (info->hw_operation == MLP)){
				if (info->id_col_name){
					free(info->id_col_name);
				}
			}
		} 
		
		if (info->filter_flag){
			if (info->filter_table_name){
				free(info->filter_table_name);
			}
			if (info->filter_col_name){
				free(info->filter_col_name);
			}
		}
		
		if (info->aggr_flag){
			if (info->aggr_table_name){
				free(info->aggr_table_name);
			}
			if (info->aggr_table_col){
				free(info->aggr_table_col);
			}
		}
	}
}

static void
extract_operation_info(char** word_array, int word_size, struct operation_info *info){
	int query_cluster = 0;
	int now_idx = 0;
	int inhib = 0;
	for (int i = 0 ; i < word_size ; ) {
		query_cluster = hw_queryhashmap(word_array[i], query_cluster);
		switch (query_cluster){
			case NONE:
				//printf("cluster: NONE\n");
				info->hw_support = false;
				if (i == 0){
					return;
				}
				i += 1;
				break;
			case SELECT:{
				//printf("cluster: SELECT\n");
				int query_check = 0;
				//printf("%s\n", word_array[i + 1]);
				query_check = hw_ophashmap(word_array[i + 1]);
				//printf("select op check - %d\n", query_check);
				if (query_check != NONE){ // madlib operation
					info->hw_support = true;
					info->hw_operation = query_check;
					//printf("operation: %d\n", info->hw_operation);
					if ((info->hw_operation == LINREGR) | (info->hw_operation == LOGREGR)){
						//printf("--regression--\n");
						//info->model_col_name = (char *)malloc(sizeof(char) * MAX_NAME_LEN);
						//strcpy(info->model_col_name, word_array[i + 2]);
						//printf("model_col_name: %s\n", info->model_col_name);
						int arr_len = 0;
						i += 2;
						if (hw_strcmp(word_array[i], (char*)"ARRAY")){
							arr_len = 0;
							while ((!hw_strcmp(word_array[i + 1 + arr_len], (char*)"FROM")) & 
								   (!hw_strcmp(word_array[i + 1 + arr_len], (char*)"ARRAY"))){
								arr_len++;
							}
							//printf("arr_len: %d\narr: ", arr_len);
							info->model_col_len = arr_len;
							info->model_col_name = (char **)malloc(sizeof(char *) * arr_len);
							for (int k = 0 ; k < arr_len ; k++){
								info->model_col_name[k] = (char *)malloc(sizeof(char) * MAX_NAME_LEN);
								strcpy(info->model_col_name[k], word_array[i + 1 + k]);
								//printf("[%s] ", info->data_col_name[k]);
							}
							//printf("\n");
							i += (1 + arr_len);
						} else if (hw_strcmp(word_array[i], (char*)"coef")){
							//printf("support? %d\n", info->hw_support);
							//printf("come----------------------------------------\n");
							arr_len = 1;
							info->model_col_len = arr_len;
							info->model_col_name = (char **)malloc(sizeof(char *) * arr_len);
							info->model_col_name[0] = (char *)malloc(sizeof(char) * MAX_NAME_LEN);
							strcpy(info->model_col_name[0], word_array[i]);
							i += arr_len;
						}						
						
						if (hw_strcmp(word_array[i], (char*)"ARRAY")){
							arr_len = 0;
							while ((!hw_strcmp(word_array[i + 1 + arr_len], (char*)"FROM")) &
								   (!hw_strcmp(word_array[i + 1 + arr_len], (char*)"ARRAY"))){
								arr_len++;
							}
							//printf("arr_len: %d\narr: ", arr_len);
							info->data_col_len = arr_len;
							info->data_col_name = (char **)malloc(sizeof(char *) * arr_len);
							for (int k = 0 ; k < arr_len ; k++){
								info->data_col_name[k] = (char *)malloc(sizeof(char) * MAX_NAME_LEN);
								strcpy(info->data_col_name[k], word_array[i + 1 + k]);
								//printf("[%s] ", info->data_col_name[k]);
							}
							//printf("\n");
							i += (1 + arr_len);
						} else if (hw_strcmp(word_array[i], (char*)"coef")){
							arr_len = 1;
							info->data_col_len = arr_len;
							info->data_col_name = (char **)malloc(sizeof(char *) * arr_len);
							info->data_col_name[0] = (char *)malloc(sizeof(char) * MAX_NAME_LEN);
							strcpy(info->data_col_name[0], word_array[i]);
							i += arr_len;
						}
					} else if ((info->hw_operation == SVM) | (info->hw_operation == MLP) | (info->hw_operation == TREE)){
						//printf("--SVM/MLP--\n");
						info->model_table_name = (char *)malloc(sizeof(char) * MAX_NAME_LEN);
						strcpy(info->model_table_name, word_array[i + 2]);
						//printf("model_table_name: %s\n", info->model_table_name);
						info->data_table_name = (char *)malloc(sizeof(char) * MAX_NAME_LEN);
						strcpy(info->data_table_name, word_array[i + 3]);
						//printf("data_table_name: %s\n", info->data_table_name);
						if ((info->hw_operation == SVM) | (info->hw_operation == MLP)){
							info->id_col_name = (char *)malloc(sizeof(char) * MAX_NAME_LEN);
							strcpy(info->id_col_name, word_array[i + 4]);
							//printf("id_col_name: %s\n", info->id_col_name);
							info->output_table_name = (char *)malloc(sizeof(char) * MAX_NAME_LEN);
							strcpy(info->output_table_name, word_array[i + 5]);	
						} else{
							info->output_table_name = (char *)malloc(sizeof(char) * MAX_NAME_LEN);
							strcpy(info->output_table_name, word_array[i + 4]);							
						}
						i += 6;
						if (info->hw_operation == MLP){
							i += 1;
						}
					} else{
						i += 1;
					}
				} else if (query_check = hw_aggrhashmap(word_array[i + 1])){ // aggr operation
					info->aggr_flag = true;
					info->aggr_operation = query_check;
					//printf("aggresion: %d\n", info->aggr_operation);

					char* aggr_table = (char *)malloc(sizeof(char) * MAX_NAME_LEN);
					strcpy(aggr_table, word_array[i + 2]);

					char* word_token = strtok(aggr_table, ".");
					int j = 0;
					while (word_token != NULL){
						if (j == 0){
							info->aggr_table_name = (char *)malloc(sizeof(char) * MAX_NAME_LEN);
							//printf("aggr1: %s\n", word_token);
							strcpy(info->aggr_table_name, word_token);
						} else if (j == 1){
							info->aggr_table_col = (char *)malloc(sizeof(char) * MAX_NAME_LEN);
							//printf("aggr2: %s\n", word_token);
							strcpy(info->aggr_table_col, word_token);
						} else{
							printf("not considered case occured\n");
							break;
						}
						j++;
						word_token = strtok(NULL, ".");
					}
					free(aggr_table);
					i += 3;
				} else{ // not supported
					info->hw_support = false;
					return;
				}
				break;
			}
			case FROM:
				//printf("cluster: FROM\n");
				if ((info->hw_support) & 
				   ((info->hw_operation == LINREGR) | (info->hw_operation == LOGREGR))){
				    info->model_table_name = (char *)malloc(sizeof(char) * MAX_NAME_LEN);
					strcpy(info->model_table_name, word_array[i + 1]);
					//printf("model_table_name: %s\n", info->model_table_name);
					info->data_table_name = (char *)malloc(sizeof(char) * MAX_NAME_LEN);
					strcpy(info->data_table_name, word_array[i + 2]);
					//printf("data_table_name: %s\n", info->data_table_name);
					i += 3;			
				} else{
					i += 1;
				}
				break;
			case WHERE:
				//printf("cluster: WHERE\n");
				info->filter_flag = true;
				char* filter_table = (char *)malloc(sizeof(char) * MAX_NAME_LEN);
				strcpy(filter_table, word_array[i + 1]);

				char* word_token = strtok(filter_table, ".");
				int j = 0;
				while (word_token != NULL){
					if (j == 0){
						info->filter_table_name = (char *)malloc(sizeof(char) * MAX_NAME_LEN);
						//printf("filter1: %s\n", word_token);
						strcpy(info->filter_table_name, word_token);
					} else if (j == 1){
						info->filter_col_name = (char *)malloc(sizeof(char) * MAX_NAME_LEN);
						//printf("filter2: %s\n", word_token);
						strcpy(info->filter_col_name, word_token);
					} else{
						printf("not considered case occured\n");
						break;
					}
					j++;
					word_token = strtok(NULL, ".");
				}
				free(filter_table);
				info->filter_operation = hw_filterhashmap(word_array[i + 2]);
				//printf("filter_operation: %d\n", info->filter_operation);
				info->filter_value = atof(word_array[i + 3]);
				//printf("filter value: %f\n", info->filter_value);
				i += 4;
				break;
			case GROUP_BY:
				//printf("cluster: GROUP_BY\n");
				info->hw_support = false;
				break;
			case ORDER_BY:
				//printf("cluster: ORDER_BY\n");
				info->hw_support = false;
				break;
			default:
				i += 1;
				break;
		}
		inhib++;
		if (inhib > 20){
			break;
		}
	}
	return;
}

int get_query_num(struct operation_info info){
	int query_num = -1;
	if (info.hw_support){
		switch (info.hw_operation){
			case (LINREGR):
				if ((info.filter_flag) & (info.aggr_flag)){
					query_num = Q4;	
				} else if (info.filter_flag){
					query_num = Q2;	
				} else if (info.aggr_flag){
					query_num = Q3;	
				} else{
					query_num = Q1;	
				}
				break;
			case (LOGREGR):
				if ((info.filter_flag) & (info.aggr_flag)){
					query_num = Q8;	
				} else if (info.filter_flag){
					query_num = Q6;	
				} else if (info.aggr_flag){
					query_num = Q7;	
				} else{
					query_num = Q5;	
				}			
				break;
			case (SVM):
				query_num = Q9;	
				break;
			case (MLP):
				query_num = Q10;	
				break;
			case (TREE):
				query_num = Q11;	
				break;		
		}
	}
	if (query_num == -1){
		printf("query classification error\n");
	}
	return query_num;
}

void printf_op_info(struct operation_info info){
	printf("\t-------operation info debugging-------\n\t");

	printf("hw_support: %s\n\t", info.hw_support ? "True" : "False");
	if (info.hw_support){
		switch (info.hw_operation){
			case LINREGR:
				printf("hw_operation: %s\n\t", "LINREGR");
				break;
			case LOGREGR:
				printf("hw_operation: %s\n\t", "LOGREGR");
				break;
			case SVM:
				printf("hw_operation: %s\n\t", "SVM");
				break;
			case MLP:
				printf("hw_operation: %s\n\t", "MLP");
				break;
			case TREE:
				printf("hw_operation: %s\n\t", "TREE");
				break;		
		}
		printf("data_table_name: %s\n\t", info.data_table_name);
		printf("model_table_name: %s\n\t", info.model_table_name);
		
		if ((info.hw_operation == LINREGR) | (info.hw_operation == LOGREGR)){
			printf("model_col_len: %d\n\t", info.model_col_len);
			printf("model_col_name: ");
			for (int i = 0 ; i < info.model_col_len ; i++){
				printf("[%s] ", info.model_col_name[i]);
			}
			printf("\n\t");
			printf("data_col_len: %d\n\t", info.data_col_len);
			printf("data_col_name: ");
			for (int i = 0 ; i < info.data_col_len ; i++){
				printf("[%s] ", info.data_col_name[i]);
			}
			printf("\n\t");
		} else if ((info.hw_operation == SVM) | (info.hw_operation == MLP) | (info.hw_operation == TREE)){
			if ((info.hw_operation == SVM) | (info.hw_operation == MLP)){
				printf("id_col_name: %s\n\t", info.id_col_name);
			}
			printf("output_table_name: %s\n\t", info.output_table_name);
		}

		if (info.filter_flag){
			printf("-------filter information exists\n\t");
			switch (info.filter_operation){
				case LARGER:
					printf("filter_flag: %s\n\t", "LARGER (>)");
					break;
				case LARGERSAME:
					printf("filter_flag: %s\n\t", "LARGERSAME (>=)");
					break;
				case SAME:
					printf("filter_flag: %s\n\t", "SAME (=)");
					break;
				case SMALLER:
					printf("filter_flag: %s\n\t", "SMALLER (<)");
					break;
				case SMALLERSAME:
					printf("filter_flag: %s\n\t", "SMALLERSAME (<=)");
					break;			
			}
			printf("filter_table_name: %s\n\t", info.filter_table_name);
			printf("filter_col_name: %s\n\t", info.filter_col_name);
			printf("filter_value: %f\n\t", info.filter_value);
		} 

		if (info.aggr_flag){
			printf("-------aggregation information exists\n\t");
			switch (info.aggr_operation){
				case COUNT:
					printf("aggr_flag: %s\n\t", "COUNT");
					break;		
				case MAX:
					printf("aggr_flag: %s\n\t", "MAX");
					break;
				case MIN:
					printf("aggr_flag: %s\n\t", "MIN");
					break;
				case AVG:
					printf("aggr_flag: %s\n\t", "AVG");
					break;
				case SUM:
					printf("aggr_flag: %s\n\t", "SUM");
					break;		
			}
			printf("aggr_table_name: %s\n\t", info.aggr_table_name);
			printf("aggr_table_col: %s\n\t", info.aggr_table_col);
		} 
	}

	printf("--------------------------------------\n");
}

// sw stack + tree table query creator functionality

static void
hw_query_modification(char* data_table_name, char* model_table_name, char* new_query) {
	strcpy(new_query, "SELECT * FROM ");
	strcat(new_query, data_table_name);
	strcat(new_query, ", ");
	strcat(new_query, model_table_name);
	strcat(new_query, ";");
}

static int64
calculate_relation_size(RelFileNode *rfn, BackendId backend, ForkNumber forknum)
{
    int64       totalsize = 0;
    char       *relationpath;
    char        pathname[MAXPGPATH];
    unsigned int segcount = 0;
 
    relationpath = relpathbackend(*rfn, backend, forknum);
 
    for (segcount = 0;; segcount++)
    {
        struct stat fst;
 
        CHECK_FOR_INTERRUPTS();
 
        if (segcount == 0)
            snprintf(pathname, MAXPGPATH, "%s",
                     relationpath);
        else
            snprintf(pathname, MAXPGPATH, "%s.%u",
                     relationpath, segcount);
 
        if (stat(pathname, &fst) < 0)
        {
            if (errno == ENOENT)
                break;
            else
                ereport(ERROR,
                        (errcode_for_file_access(),
                         errmsg("could not stat file \"%s\": %m", pathname)));
        }
		printf("stat_check: %ld (%d)\n", fst.st_size, segcount);
        totalsize += fst.st_size;
    }

	return totalsize;
}

static int64
calculate_toast_table_size(Oid toastrelid)
{
    int64       size = 0;
    Relation    toastRel;
    ForkNumber  forkNum;
    ListCell   *lc;
    List       *indexlist;
 
    toastRel = relation_open(toastrelid, AccessShareLock);
 
    /* toast heap size, including FSM and VM size */
    for (forkNum = 0; forkNum <= MAX_FORKNUM; forkNum++)
        size += calculate_relation_size(&(toastRel->rd_node),
                                        toastRel->rd_backend, forkNum);
 
    /* toast index size, including FSM and VM size */
    indexlist = RelationGetIndexList(toastRel);
 
    /* Size is calculated using all the indexes available */
    foreach(lc, indexlist)
    {
        Relation    toastIdxRel;
 
        toastIdxRel = relation_open(lfirst_oid(lc),
                                    AccessShareLock);
        for (forkNum = 0; forkNum <= MAX_FORKNUM; forkNum++)
            size += calculate_relation_size(&(toastIdxRel->rd_node),
                                            toastIdxRel->rd_backend, forkNum);
 
        relation_close(toastIdxRel, AccessShareLock);
    }
    list_free(indexlist);
    relation_close(toastRel, AccessShareLock);
 
	return size;
}

static int64
calculate_table_size(Relation rel)
{
    int64       size = 0;
    ForkNumber  forkNum;
    /*
     * heap size, including FSM and VM
     */
    for (forkNum = 0; forkNum <= MAX_FORKNUM; forkNum++)
        size += calculate_relation_size(&(rel->rd_node), rel->rd_backend,
                                        forkNum);
    /*
     * Size of toast relation
     */
    if (OidIsValid(rel->rd_rel->reltoastrelid))
        size += calculate_toast_table_size(rel->rd_rel->reltoastrelid);
 
	return size;
 }

static int
hw_get_table_size(int oid) {
	Oid relOid = oid;
	Relation rel;
	int64 size;
	rel = try_relation_open(relOid, AccessShareLock);
	
	if(rel != NULL)
		size = calculate_table_size(rel);
	
	relation_close(rel, AccessShareLock);
	return size;
}

static void
hw_rtable_extract(Query* query, int* rtable_id, int* rtable_relid, char** rtable_name, int* rtable_colnum, unsigned long long int* rtable_colsel, char*** rtable_colname, int *table_size) {
	ListCell* rtable_list;

	int idx = 0;
	foreach(rtable_list, query->rtable) {
		//printf("hw stack debug - hw_rtable_extract\nidx: %d\n", idx);
		RangeTblEntry* rtbl = lfirst_node(RangeTblEntry, rtable_list);
		
		rtable_id[idx] = idx;
		rtable_relid[idx] = rtbl->relid;
		rtable_name[idx] = (char *)malloc(sizeof(char *) * strlen(rtbl->eref->aliasname));
		strcpy(rtable_name[idx], rtbl->eref->aliasname);

		int col_num = list_length(rtbl->eref->colnames);
		rtable_colnum[idx] = col_num;
		rtable_colsel[idx] = *(rtbl->selectedCols->words);
		rtable_colname[idx] = (char**)malloc(sizeof(char*)*col_num); 
		
		ListCell* columns;
		int col_idx = 0;	
		foreach(columns, rtbl->eref->colnames) {
			char* colname = strVal(lfirst(columns));
			rtable_colname[idx][col_idx] = (char *)malloc(sizeof(char *) * strlen(colname));
			strcpy(rtable_colname[idx][col_idx], colname);
			col_idx++;			
		}
		//printf("check, arr: %d, data: %d\n", rtable_relid[idx], rtbl->relid);
		table_size[idx] = hw_get_table_size(rtable_relid[idx]);
		idx++;
	}
}

static void
hw_str_delete(char* str, char ch) {
	for(; *str!='\0'; str++) {
		if(*str == ch) {
			strcpy(str, str+1);
			str--;
		}
	}
}

// memory dump functionality

static void 
printchar(unsigned char c){
	if (isprint(c)){
 		printf("%c", c);
	}
 	else{
 		printf(".");
	}
}

static void 
dumpmem(unsigned char *buff, int len){
	int i;
	for (i = 0 ; i < len ; i++){
		if (i % 16 == 0){
			printf("0x%08x ", &buff[i]);
		}
		printf("%02x ", buff[i]);
		if (i % 16 - 15 == 0){
			int j;
			printf("" "");
			for (j = i - 15 ; j <= i ; j++){
				printchar(buff[j]);
			}
			printf("\n");
		}
	}
	if (i % 16 != 0){
		int j;
		int spaces = (len - i + 16 - i % 16)*3 + 2;
		for (j = 0 ; j < spaces ; j++){
			printf("" ""); 
		}
		for(j = i - (i % 16) ; j < len ; j++){
			printchar(buff[j]);
		}
	}
	printf("\n");
} 

// sw stack + tree table query creator functionality

static Page
get_page_from_raw(bytea *raw_page)
{
	Page		page;
	int			raw_page_size;

	raw_page_size = VARSIZE_ANY_EXHDR(raw_page);

	if (raw_page_size != BLCKSZ)
		ereport(ERROR,
				(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
				 errmsg("invalid page size"),
				 errdetail("Expected %d bytes, got %d.",
						   BLCKSZ, raw_page_size)));

	page = palloc(raw_page_size);

	memcpy(page, VARDATA_ANY(raw_page), raw_page_size);

	return page;
}

static bytea *
get_raw_from_rel(Relation rel){
	bytea	   *raw_page; 
	char	   *raw_page_data;
	Buffer		buf;

	raw_page = (bytea *) palloc(BLCKSZ + VARHDRSZ);
	SET_VARSIZE(raw_page, BLCKSZ + VARHDRSZ);
	raw_page_data = VARDATA(raw_page);

	buf = ReadBufferExtended(rel, MAIN_FORKNUM, 0, RBM_NORMAL, NULL);
	LockBuffer(buf, BUFFER_LOCK_SHARE);

	memcpy(raw_page_data, BufferGetPage(buf), BLCKSZ);

	LockBuffer(buf, BUFFER_LOCK_UNLOCK);
	ReleaseBuffer(buf);

	return raw_page;
}

static bytea *
get_raw_from_rel_with_bias(Relation rel, int cnt){
	bytea	   *raw_page; 
	char	   *raw_page_data;
	Buffer		buf;

	raw_page = (bytea *) palloc(BLCKSZ + VARHDRSZ);
	SET_VARSIZE(raw_page, BLCKSZ + VARHDRSZ);
	raw_page_data = VARDATA(raw_page);

	buf = ReadBufferExtended(rel, MAIN_FORKNUM, cnt, RBM_NORMAL, NULL);

	LockBuffer(buf, BUFFER_LOCK_SHARE);

	memcpy(raw_page_data, BufferGetPage(buf), BLCKSZ);

	LockBuffer(buf, BUFFER_LOCK_UNLOCK);
	ReleaseBuffer(buf);

	return raw_page;
}

static void 
int_debug_print(int* variable, int var_len, int typeflag){ // 0 for int / 1 for hex
	int linecnt = 0;
	for (int print_i = 0 ; print_i < var_len ; print_i++){
		if (linecnt >= 10){
			printf("\n");
			linecnt = 0;
		} else {
			if (print_i != 0){
				printf(" ");
			}
		}

		if (typeflag == 0){
			printf("%4d ", variable[print_i]);
		} else if (typeflag == 1){
			printf("%4x ", variable[print_i]);
		}
		linecnt++;
	}
	printf("\n");
}

static void 
float_debug_print(float* variable, int var_len, int typeflag){ // 0 for float / 1 for hex
	int linecnt = 0;
	for (int print_i = 0 ; print_i < var_len ; print_i++){
		if (linecnt >= 10){
			printf("\n");
			linecnt = 0;
		} else {
			if (print_i != 0){
				printf(" ");
			}
		}

		if (typeflag == 0){
			printf("%10f", variable[print_i]);
		} else if (typeflag == 1){
			printf("%4x", variable[print_i]);
		}

		linecnt++;
	}
	printf("\n");
}

static char *
addr_auto_padder(ItemId item_id, char* now_data_addr, char *item_base_addr, int num_nodes, int data_size){
	int now_filled = (now_data_addr - item_base_addr);
	int will_filled = num_nodes * data_size;
	//printf("%d %d %d\n", now_filled, will_filled, item_id->lp_len);
	if (now_filled + will_filled >= item_id->lp_len){
		// item change will occur
		int remain = item_id->lp_len - now_filled;
		int padding = remain % data_size;
		//printf("padding %d\n", padding);
		return now_data_addr + padding;
	} else{
		return now_data_addr;
	}
}

static bool 
carefully_incl_addr(ItemId item_id, char* item_base_addr, char *now_data_addr, int incl_num){
	if (now_data_addr + incl_num >= item_base_addr + item_id->lp_len){
		printf("-------item change tried-------\n");
		//printf("item_base_addr: %p\nitem_boubdary: %p\nnow_data_addr: %p\nincl_result: %p\n", item_base_addr, item_base_addr + item_id->lp_len, now_data_addr, now_data_addr + incl_num);
		//printf("-----------------------------\n");
		return false;
	} else{
		return true;
	}
}

static char*
tree_table_query_creator(){

	printf("creator!\n");

	char *train_select_query = (char *)malloc(sizeof(char) * 100);
	strcpy(train_select_query, "SELECT * FROM ");
	strcat(train_select_query, tree_table_name);
	strcat(train_select_query, ";");	
	free(tree_table_name);

	printf("using query: %s\n", train_select_query);

	start_xact_command();

	List *parsetree_list_tree;
	ListCell *parsetree_item_tree;
	List *querytree_list_tree;
	parsetree_list_tree = pg_parse_query(train_select_query);
	//MemoryContextSwitchTo(oldcontext);
	foreach(parsetree_item_tree, parsetree_list_tree) {
		RawStmt *parsetree_tree = lfirst_node(RawStmt, parsetree_item_tree);
		querytree_list_tree = pg_analyze_and_rewrite(parsetree_tree, train_select_query, NULL, 0, NULL);
	}
	
	//TRACE_POSTGRESQL_QUERY_DONE(train_select_query);
	ListCell* query_list_tree;
	ListCell* rtable_list;
	Oid tree_table_oid;
	foreach(query_list_tree, querytree_list_tree){
		Query* query = lfirst_node(Query, query_list_tree);
		foreach(rtable_list, query->rtable) {
			RangeTblEntry* rtbl = lfirst_node(RangeTblEntry, rtable_list);
			tree_table_oid = rtbl->relid;
		}
	}
	free(train_select_query);
	
	printf("tree_table_creator - oid: %d\n", tree_table_oid);
	Relation tree_table;
	if (!(tree_table = try_relation_open(tree_table_oid, AccessShareLock))){
		printf("tree_table_creator - Oid error occured\n");
	}
	
	// Toast raw table check
	if (OidIsValid(tree_table->rd_rel->reltoastrelid)){
		Oid tree_data_table_oid = tree_table->rd_rel->reltoastrelid;
		Relation tree_data_table;

		if (!(tree_data_table = try_relation_open(tree_data_table_oid, AccessShareLock))){
			printf("hw stack debug - TOAST Oid error occured\n");
		}
		bytea *tree_data_raw_page = get_raw_from_rel(tree_data_table);
		relation_close(tree_data_table, AccessShareLock);

		Page tree_data_page = get_page_from_raw(tree_data_raw_page);
		int tree_data_item_num = PageGetMaxOffsetNumber(tree_data_page);
		PageHeader tree_data_page_header = (PageHeader) tree_data_page;
		LocationIndex tree_data_page_lower = tree_data_page_header->pd_lower;
		LocationIndex tree_data_page_upper = tree_data_page_header->pd_upper;	
		
		printf("tree_data_extractor - toast page debug\ntree_table_lower: %x\ntree_table_upper: %x\ntree_data_item_num: %d\n", 
							tree_data_page_lower, tree_data_page_upper, tree_data_item_num);

		int toast_now_item_offset = 1;
		ItemId toast_now_item_id = PageGetItemId(tree_data_page, toast_now_item_offset);
		char *toast_item_rawdata = ((char *) PageGetItem(tree_data_page, toast_now_item_id));
		HeapTupleHeader toast_item_header = (HeapTupleHeader) toast_item_rawdata;
		
		char *now_data_addr = toast_item_rawdata + SizeofHeapTupleHeader + 17;
		//printf("addr offset: %x\n", (char *)now_data_addr - (char *)tree_data_page);
		uint16_t tree_depth = *((uint16_t *)(now_data_addr));
		int num_datas = 7;
		if (!carefully_incl_addr(toast_now_item_id, toast_item_rawdata, now_data_addr, 2)){
			// item change
			if ((toast_now_item_offset + 1) <= tree_data_item_num){
				toast_now_item_offset++;
				toast_now_item_id = PageGetItemId(tree_data_page, toast_now_item_offset);
				toast_item_rawdata = ((char *) PageGetItem(tree_data_page, toast_now_item_id));
				toast_item_header = (HeapTupleHeader) toast_item_rawdata;
				now_data_addr = toast_item_rawdata + SizeofHeapTupleHeader + 13;
			} else{
				printf("tree_data_extractor - item number error in toast page, want %d but max %d\n", toast_now_item_offset + 1, tree_data_item_num);
			}
		} else{
			now_data_addr += 2;
		}
		//printf("addr offset: %x\n", (char *)now_data_addr - (char *)tree_data_page);
		uint16_t n_y_labels = *((uint16_t *)(now_data_addr));
		if (!carefully_incl_addr(toast_now_item_id, toast_item_rawdata, now_data_addr, 2)){
			// item change
			if ((toast_now_item_offset + 1) <= tree_data_item_num){
				toast_now_item_offset++;
				toast_now_item_id = PageGetItemId(tree_data_page, toast_now_item_offset);
				toast_item_rawdata = ((char *) PageGetItem(tree_data_page, toast_now_item_id));
				toast_item_header = (HeapTupleHeader) toast_item_rawdata;
				now_data_addr = toast_item_rawdata + SizeofHeapTupleHeader + 13;
			} else{
				printf("tree_data_extractor - item number error in toast page, want %d but max %d\n", toast_now_item_offset + 1, tree_data_item_num);
			}
		} else{
			now_data_addr += 2;
		}
 		//printf("addr offset: %x\n", (char *)now_data_addr - (char *)tree_data_page);
		if (!carefully_incl_addr(toast_now_item_id, toast_item_rawdata, now_data_addr, 2)){
			// item change
			if ((toast_now_item_offset + 1) <= tree_data_item_num){
				toast_now_item_offset++;
				toast_now_item_id = PageGetItemId(tree_data_page, toast_now_item_offset);
				toast_item_rawdata = ((char *) PageGetItem(tree_data_page, toast_now_item_id));
				toast_item_header = (HeapTupleHeader) toast_item_rawdata;
				now_data_addr = toast_item_rawdata + SizeofHeapTupleHeader + 13;
			} else{
				printf("tree_data_extractor - item number error in toast page, want %d but max %d\n", toast_now_item_offset + 1, tree_data_item_num);
			}
		} else{
			now_data_addr += 2;
		}
    	//printf("addr offset: %x\n", (char *)now_data_addr - (char *)tree_data_page);
		if (!carefully_incl_addr(toast_now_item_id, toast_item_rawdata, now_data_addr, 2)){
			// item change
			if ((toast_now_item_offset + 1) <= tree_data_item_num){
				toast_now_item_offset++;
				toast_now_item_id = PageGetItemId(tree_data_page, toast_now_item_offset);
				toast_item_rawdata = ((char *) PageGetItem(tree_data_page, toast_now_item_id));
				toast_item_header = (HeapTupleHeader) toast_item_rawdata;
				now_data_addr = toast_item_rawdata + SizeofHeapTupleHeader + 13;
			} else{
				printf("tree_data_extractor - item number error in toast page, want %d but max %d\n", toast_now_item_offset + 1, tree_data_item_num);
			}
		} else{
			now_data_addr += 2;
		}
    	//printf("addr offset: %x\n", (char *)now_data_addr - (char *)tree_data_page);
		if (!carefully_incl_addr(toast_now_item_id, toast_item_rawdata, now_data_addr, 4)){
			// item change
			if ((toast_now_item_offset + 1) <= tree_data_item_num){
				toast_now_item_offset++;
				toast_now_item_id = PageGetItemId(tree_data_page, toast_now_item_offset);
				toast_item_rawdata = ((char *) PageGetItem(tree_data_page, toast_now_item_id));
				toast_item_header = (HeapTupleHeader) toast_item_rawdata;
				now_data_addr = toast_item_rawdata + SizeofHeapTupleHeader + 13;
			} else{
				printf("tree_data_extractor - item number error in toast page, want %d but max %d\n", toast_now_item_offset + 1, tree_data_item_num);
			}
		} else{
			now_data_addr += 4;
		}
		
		int num_nodes = pow(2,tree_depth) - 1;
		printf("tree_data_extractor - toast page data debug\ntree_depth: %d\nn_y_labels: %d\nnum_nodes: %d\n", 
										tree_depth, n_y_labels, num_nodes);

		now_data_addr = addr_auto_padder(toast_now_item_id, now_data_addr, toast_item_rawdata, num_nodes, 4);
		//printf("addr offset: %x\n", (char *)now_data_addr - (char *)tree_data_page);
		int* feature_indices = (int *) malloc(sizeof(int) * num_nodes);
		for (int feature_indices_i = 0 ; feature_indices_i < num_nodes ; feature_indices_i++){
			feature_indices[feature_indices_i] = *((int *)(now_data_addr));
			if (!carefully_incl_addr(toast_now_item_id, toast_item_rawdata, now_data_addr, 4)){
				// item change
				if ((toast_now_item_offset + 1) <= tree_data_item_num){
					toast_now_item_offset++;
					toast_now_item_id = PageGetItemId(tree_data_page, toast_now_item_offset);
					toast_item_rawdata = ((char *) PageGetItem(tree_data_page, toast_now_item_id));
					toast_item_header = (HeapTupleHeader) toast_item_rawdata;
					now_data_addr = toast_item_rawdata + SizeofHeapTupleHeader + 13;
					now_data_addr = addr_auto_padder(toast_now_item_id, now_data_addr, toast_item_rawdata, num_nodes - feature_indices_i - 1, 4);
				} else{
					printf("tree_data_extractor - item number error in toast page, want %d but max %d\n", toast_now_item_offset + 1, tree_data_item_num);
				}
			} else{
				now_data_addr += 4;
			}
		}
		printf("feature_indices\n");
		int_debug_print(feature_indices, num_nodes, 0);

		now_data_addr = addr_auto_padder(toast_now_item_id, now_data_addr, toast_item_rawdata, num_nodes, 8);
		//printf("addr offset: %x\n", (char *)now_data_addr - (char *)tree_data_page);
		float* feature_thresholds = (float *) malloc(sizeof(float) * num_nodes);
		for (int feature_thresholds_i = 0 ; feature_thresholds_i < num_nodes ; feature_thresholds_i++){
			feature_thresholds[feature_thresholds_i] = (float) *((double *)(now_data_addr));
			if (!carefully_incl_addr(toast_now_item_id, toast_item_rawdata, now_data_addr, 8)){
				// item change
				if ((toast_now_item_offset + 1) <= tree_data_item_num){
					toast_now_item_offset++;
					toast_now_item_id = PageGetItemId(tree_data_page, toast_now_item_offset);
					toast_item_rawdata = ((char *) PageGetItem(tree_data_page, toast_now_item_id));
					toast_item_header = (HeapTupleHeader) toast_item_rawdata;
					now_data_addr = toast_item_rawdata + SizeofHeapTupleHeader + 13;
					now_data_addr = addr_auto_padder(toast_now_item_id, now_data_addr, toast_item_rawdata, num_nodes - feature_thresholds_i - 1, 8);
				} else{
					printf("tree_data_extractor - item number error in toast page, want %d but max %d\n", toast_now_item_offset + 1, tree_data_item_num);
				}
			} else{
				now_data_addr += 8;
			}
		}
		printf("feature_thresholds\n");
		float_debug_print(feature_thresholds, num_nodes, 0);

		now_data_addr = addr_auto_padder(toast_now_item_id, now_data_addr, toast_item_rawdata, num_nodes, 4);
		//printf("addr offset: %x\n", (char *)now_data_addr - (char *)tree_data_page);
		for (int is_categorical_i = 0 ; is_categorical_i < num_nodes ; is_categorical_i++){
			if (!carefully_incl_addr(toast_now_item_id, toast_item_rawdata, now_data_addr, 4)){
				// item change
				if ((toast_now_item_offset + 1) <= tree_data_item_num){
					toast_now_item_offset++;
					toast_now_item_id = PageGetItemId(tree_data_page, toast_now_item_offset);
					toast_item_rawdata = ((char *) PageGetItem(tree_data_page, toast_now_item_id));
					toast_item_header = (HeapTupleHeader) toast_item_rawdata;
					now_data_addr = toast_item_rawdata + SizeofHeapTupleHeader + 13;
					now_data_addr = addr_auto_padder(toast_now_item_id, now_data_addr, toast_item_rawdata, num_nodes - is_categorical_i - 1, 4);
				} else{
					printf("tree_data_extractor - item number error in toast page, want %d but max %d\n", toast_now_item_offset + 1, tree_data_item_num);
				}
			} else{
				now_data_addr += 4;
			}
		}
		printf("is_categorical\n");

		now_data_addr = addr_auto_padder(toast_now_item_id, now_data_addr, toast_item_rawdata, num_nodes * 2, 8);
		//printf("addr offset: %x\n", (char *)now_data_addr - (char *)tree_data_page);
		for (int nonnull_split_count_i = 0 ; nonnull_split_count_i < (num_nodes * 2) ; nonnull_split_count_i++){
			if (!carefully_incl_addr(toast_now_item_id, toast_item_rawdata, now_data_addr, 8)){
				// item change
				if ((toast_now_item_offset + 1) <= tree_data_item_num){
					toast_now_item_offset++;
					toast_now_item_id = PageGetItemId(tree_data_page, toast_now_item_offset);
					toast_item_rawdata = ((char *) PageGetItem(tree_data_page, toast_now_item_id));
					toast_item_header = (HeapTupleHeader) toast_item_rawdata;
					now_data_addr = toast_item_rawdata + SizeofHeapTupleHeader + 13;
					now_data_addr = addr_auto_padder(toast_now_item_id, now_data_addr, toast_item_rawdata, (num_nodes * 2) - nonnull_split_count_i - 1, 8);
				} else{
					printf("tree_data_extractor - item number error in toast page, want %d but max %d\n", toast_now_item_offset + 1, tree_data_item_num);
				}
			} else{
				now_data_addr += 8;
			}
		}
		printf("nonnull_split_count\n");

		now_data_addr = addr_auto_padder(toast_now_item_id, now_data_addr, toast_item_rawdata, num_nodes * 3, 8);
		//printf("addr offset: %x\n", (char *)now_data_addr - (char *)tree_data_page);
		float** predictions = (float **) malloc(sizeof(float *) * 3);
		for (int malloc_i = 0 ; malloc_i < 3 ; malloc_i++){
			predictions[malloc_i] = (float *) malloc(sizeof(float) * num_nodes);
		}
		for (int predictions_line = 0 ; predictions_line < 3 ; predictions_line++){
			for (int predictions_i = 0 ; predictions_i < num_nodes ; predictions_i++){
				predictions[predictions_line][predictions_i] = (float) *((double *)(now_data_addr));
				if (!carefully_incl_addr(toast_now_item_id, toast_item_rawdata, now_data_addr, 8)){
					// item change
					if ((toast_now_item_offset + 1) <= tree_data_item_num){
						toast_now_item_offset++;
						toast_now_item_id = PageGetItemId(tree_data_page, toast_now_item_offset);
						toast_item_rawdata = ((char *) PageGetItem(tree_data_page, toast_now_item_id));
						toast_item_header = (HeapTupleHeader) toast_item_rawdata;
						now_data_addr = toast_item_rawdata + SizeofHeapTupleHeader + 13;
						now_data_addr = addr_auto_padder(toast_now_item_id, now_data_addr, toast_item_rawdata, (num_nodes * (3 - predictions_line)) - predictions_i - 1, 8);
					} else{
						//printf("tree_data_extractor - item number error in toast page, want %d but max %d\n", toast_now_item_offset + 1, tree_data_item_num);
						printf("end of page\n");
					}
				} else{
					now_data_addr += 8;
				}
			}
		}
		
		printf("predictions\n");
		for (int pline = 0 ; pline < 3 ; pline++){
			printf("line %d\n", pline);
			float_debug_print(predictions[pline], num_nodes, 0);
		}

		// make query
		printf("make query for new table\n");

		// make query for drop table
		char *drop_query = (char *) malloc(sizeof(char) * 40);
		char *drop_query_front = "DROP TABLE IF EXISTS higgs_1k_for_hw;";
		strcpy(drop_query, drop_query_front);
		//printf("drop_query: %s\n", drop_query);

		// make query for create table
		char *create_query = (char *) malloc(sizeof(char) * (50 + num_datas * (num_nodes * 15)));
		char *create_query_front = "CREATE TABLE higgs_1k_for_hw(d0 int, d1 int, ";
		char *create_query_end = ");";
		char *col_data_front = "d";
		char *col_dash = "_";
		char *create_comma = ", ";
		char *col_type_int = " int";
		char *col_type_float = " real";

		strcpy(create_query, create_query_front);

		char *create_query_tmp = (char *) malloc(sizeof(char) * 15);
		char *create_col_tmp = (char *) malloc(sizeof(char) * 10);
		char *create_data_num_tmp = (char *) malloc(sizeof(char) * 5);
		char *create_col_num_tmp = (char *) malloc(sizeof(char) * 5);

		for (int data_num = 2 ; data_num < num_datas ; data_num++){
			strcpy(create_col_tmp, col_data_front);
			sprintf(create_data_num_tmp, "%d", data_num);
			strcat(create_col_tmp, create_data_num_tmp);
			strcat(create_col_tmp, col_dash);
			for (int col_num = 0 ; col_num < num_nodes ; col_num++){
				strcpy(create_query_tmp, create_col_tmp);
				sprintf(create_col_num_tmp, "%d", col_num);
				strcat(create_query_tmp, create_col_num_tmp);
				if (data_num == 2){
					strcat(create_query_tmp, col_type_int);
				} else{
					strcat(create_query_tmp, col_type_float);
				}
				if ((col_num < (num_nodes - 1)) | (data_num < (num_datas - 1))){
					strcat(create_query_tmp, create_comma);
				}
				strcat(create_query, create_query_tmp);	
			}
		}
		free(create_query_tmp);
		free(create_col_tmp);
		free(create_data_num_tmp);
		free(create_col_num_tmp);

		strcat(create_query, create_query_end);
		//printf("create_query: %s\n", create_query);

		// make query for save data to table
		char *save_query = malloc(sizeof(char) * (40 + 7 * (num_nodes * 15)));
		char *save_num_tmp = (char *) malloc(sizeof(char) * 10);
		char *save_query_front = "INSERT INTO higgs_1k_for_hw VALUES(";
		char *save_query_end = ");";
		char *save_comma = ", ";
		strcpy(save_query, save_query_front);

		for (int data_num = 0 ; data_num < num_datas ; data_num++){  
			if (data_num == 0){
				sprintf(save_num_tmp, "%d", tree_depth);
				strcat(save_query, save_num_tmp);
				strcat(save_query, save_comma);
			} else if (data_num == 1){
				sprintf(save_num_tmp, "%d", n_y_labels);
				strcat(save_query, save_num_tmp);
				strcat(save_query, save_comma);
			} else{
				for (int col_num = 0 ; col_num < num_nodes ; col_num++){
					switch (data_num){
						case 2:
							sprintf(save_num_tmp, "%d", feature_indices[col_num]);
							break;
						case 3:
							sprintf(save_num_tmp, "%f", feature_thresholds[col_num]);
							break;
						case 4:
							sprintf(save_num_tmp, "%f", predictions[0][col_num]);
							break;
						case 5:
							sprintf(save_num_tmp, "%f", predictions[1][col_num]);
							break;
						case 6:
							sprintf(save_num_tmp, "%f", predictions[2][col_num]);
							break;                    
					}
					strcat(save_query, save_num_tmp);
					if ((col_num < (num_nodes - 1)) | (data_num < (num_datas - 1))){
						strcat(save_query, save_comma);
					} 
				}
			}
		}
		free(save_num_tmp);

		strcat(save_query, save_query_end);	
		//printf("%s\n", save_query);

		char* total_query = (char *) malloc(sizeof(char) * (strlen(drop_query) + strlen(create_query) + strlen(save_query) + 5));
		strcpy(total_query, drop_query);
		strcat(total_query, create_query);
		strcat(total_query, save_query);
		free(drop_query);
		free(create_query);
		free(save_query);

		return total_query;

	} else{
		printf("error - no toast relation in tree table\n");
	}
	relation_close(tree_table, AccessShareLock);

	finish_xact_command();
	return train_select_query;
}

static double
get_data_num(Oid table_oid, int table_size, double *page_num){
	
	printf("-- get_data_num -- OID = %d\n", table_oid);

	Relation table_rel;
	if (!(table_rel = try_relation_open(table_oid, AccessShareLock))){
		printf("get_data_num - Oid error occured\n");
	}

	char pathname[MAXPGPATH];
	char *relationpath = relpathbackend(table_rel->rd_node, table_rel->rd_backend, 0);
	struct stat fst;
	snprintf(pathname, MAXPGPATH, "%s", relationpath);
	if (stat(pathname, &fst) < 0){
		if (errno != ENOENT){
			ereport(ERROR,
					(errcode_for_file_access(),
						errmsg("could not stat file \"%s\": %m", pathname)));
		}
	}
	double total_page_num = fst.st_size/0x2000;
	*page_num = total_page_num;
	double total_data_num = 0;
	double first_page_size = PageGetMaxOffsetNumber(get_page_from_raw(get_raw_from_rel(table_rel)));
	printf("model page data (first page): %f\n", first_page_size);

	if (total_page_num == 1){
		total_data_num = first_page_size;
	} else{
		double last_page_size = PageGetMaxOffsetNumber(get_page_from_raw(get_raw_from_rel_with_bias(table_rel, (total_page_num - 1))));
		printf("model page data (last page): %f\n", last_page_size);
		total_data_num = first_page_size * (total_page_num - 1) + last_page_size;
	}

	relation_close(table_rel, AccessShareLock);

	return total_data_num;
}

static double 
get_hw_expectation_time(int user_query_num, int user_dataset, double user_pagenum){

	// Query configuration
	const size_t user_query = user_query_num;

	//	BIW resource model
	const size_t user_total_lut  = USER_TOTAL_LUT;
	const size_t user_total_ff	 = USER_TOTAL_FF;
	const size_t user_total_uram = USER_TOTAL_URAM;
	const size_t user_total_bram = USER_TOTAL_BRAM;
	const size_t user_total_dsp  = USER_TOTAL_DSP;

	//	Resource check
	size_t user_core_lut  = user_total_lut - SMARTSSD_CORE_CONST_LUT;
	size_t user_core_ff   = user_total_ff - SMARTSSD_CORE_CONST_FF;
	size_t user_core_uram = user_total_uram - SMARTSSD_CORE_CONST_URAM;
	size_t user_core_bram = user_total_bram - SMARTSSD_CORE_CONST_BRAM;
	size_t user_core_dsp  = user_total_dsp - SMARTSSD_CORE_CONST_DSP;

	size_t user_corenum_lut  = user_core_lut/SMARTSSD_CORE_VAR_LUT;
	size_t user_corenum_ff   = user_core_ff/SMARTSSD_CORE_VAR_FF;
	size_t user_corenum_uram = user_core_uram/SMARTSSD_CORE_VAR_URAM;
	size_t user_corenum_bram = user_core_bram/SMARTSSD_CORE_VAR_BRAM;
	size_t user_corenum_dsp  = user_core_dsp/SMARTSSD_CORE_VAR_DSP;

	size_t user_corenum_resource[5] = {user_corenum_lut, user_corenum_ff, user_corenum_uram, user_corenum_bram, user_corenum_dsp};

	size_t user_corenum = user_corenum_resource[0];
	for(int i=1; i<5; i++) {
		if(user_corenum >= user_corenum_resource[i])
			user_corenum = user_corenum_resource[i];
	}

	//	BIW timing model
	const size_t user_database_size = ((long long)user_pagenum + 1)*8*1024;
	const size_t user_ssd2fpga_bw = USER_SSD2FPGA_BW;
	const size_t user_dram2fpga_bw = USER_DRAM2FPGA_BW*USER_DRAM_CH;
	const size_t user_fpga2host_bw = USER_FPGA2HOST_BW;

	size_t user_ssd2fpga_factor = user_ssd2fpga_bw/SMARTSSD_SSD2FPGA_BW;
	size_t user_dram2fpga_factor = user_dram2fpga_bw/SMARTSSD_DRAM2FPGA_BW;
	size_t user_fpga2host_factor = user_fpga2host_bw/SMARTSSD_FPGA2HOST_BW;

	size_t host_iteration = user_database_size/((long long)UNIT_DATABASE_SIZE*2);
	size_t page_iteration = (user_database_size-host_iteration*UNIT_DATABASE_SIZE*2)/PAGE_SIZE;

	// Host static time expectation: address mapping, setkernel
	const double host_addressmap_latency = HOST_ADDRESSMAP_LATENCY;
	double host_total_addressmap_latency = host_addressmap_latency*(host_iteration+1);
	const double host_setkernel_latency = HOST_SETKERNEL_LATENCY;
	double host_total_setkernel_latency = host_setkernel_latency*(host_iteration+1);

	// Host dynamic time expectation: CreateBuffer
	size_t user_lastdatabase_size = user_database_size - host_iteration*UNIT_DATABASE_SIZE*2;

	double host_createbuffer_latency = 0;
	if(user_lastdatabase_size <= SMARTSSD_DATABASE_SIZE_STD_4)
		host_createbuffer_latency = HOST_CREATEBUF_LATENCY_4;
	else if(user_lastdatabase_size > SMARTSSD_DATABASE_SIZE_STD_4 && user_lastdatabase_size <= SMARTSSD_DATABASE_SIZE_STD_3)
		host_createbuffer_latency = HOST_CREATEBUF_LATENCY_4*user_lastdatabase_size/SMARTSSD_DATABASE_SIZE_STD_4;
	else if(user_lastdatabase_size > SMARTSSD_DATABASE_SIZE_STD_3 && user_lastdatabase_size <= SMARTSSD_DATABASE_SIZE_STD_2)
		host_createbuffer_latency = HOST_CREATEBUF_LATENCY_3*user_lastdatabase_size/SMARTSSD_DATABASE_SIZE_STD_3;
	else if(user_lastdatabase_size > SMARTSSD_DATABASE_SIZE_STD_2 && user_lastdatabase_size <= SMARTSSD_DATABASE_SIZE_STD_1)
		host_createbuffer_latency = HOST_CREATEBUF_LATENCY_2*user_lastdatabase_size/SMARTSSD_DATABASE_SIZE_STD_2;
	else if(user_lastdatabase_size > SMARTSSD_DATABASE_SIZE_STD_1 && user_lastdatabase_size <= SMARTSSD_DATABASE_SIZE_STD_0)
		host_createbuffer_latency = HOST_CREATEBUF_LATENCY_1*user_lastdatabase_size/SMARTSSD_DATABASE_SIZE_STD_1;		
	else
		host_createbuffer_latency = HOST_CREATEBUF_LATENCY_0*user_lastdatabase_size/SMARTSSD_DATABASE_SIZE_STD_0;

	double host_total_createbuffer_latency = (host_iteration)*HOST_CREATEBUF_LATENCY_0*UNIT_DATABASE_SIZE*2/SMARTSSD_DATABASE_SIZE_STD_0;
	for(int i=0; i<host_iteration+1; i++) {
		if(i==host_iteration && host_iteration!=0)
			host_total_createbuffer_latency = host_total_createbuffer_latency + host_createbuffer_latency + 100;
		else if(i==host_iteration && host_iteration==0)
			host_total_createbuffer_latency = host_total_createbuffer_latency + host_createbuffer_latency;
		else
			host_total_createbuffer_latency = host_total_createbuffer_latency + 100;
	}

	// Data transfer time (SSD2FPGA) time expectation
	double user_ssd2fpga_effbw;
	if(user_lastdatabase_size <= SMARTSSD_DATABASE_SIZE_STD_4)
		user_ssd2fpga_effbw = SMARTSSD_SSD2FPGA_EFFBW_4;
	else if(user_lastdatabase_size > SMARTSSD_DATABASE_SIZE_STD_4 && user_lastdatabase_size <= SMARTSSD_DATABASE_SIZE_STD_3)
		user_ssd2fpga_effbw = SMARTSSD_SSD2FPGA_EFFBW_4*user_lastdatabase_size/SMARTSSD_DATABASE_SIZE_STD_4;
	else if(user_lastdatabase_size > SMARTSSD_DATABASE_SIZE_STD_3 && user_lastdatabase_size <= SMARTSSD_DATABASE_SIZE_STD_2)
		user_ssd2fpga_effbw = SMARTSSD_SSD2FPGA_EFFBW_3*user_lastdatabase_size/SMARTSSD_DATABASE_SIZE_STD_3;
	else if(user_lastdatabase_size > SMARTSSD_DATABASE_SIZE_STD_2 && user_lastdatabase_size <= SMARTSSD_DATABASE_SIZE_STD_1)
		user_ssd2fpga_effbw = SMARTSSD_SSD2FPGA_EFFBW_2*user_lastdatabase_size/SMARTSSD_DATABASE_SIZE_STD_2;
	else if(user_lastdatabase_size > SMARTSSD_DATABASE_SIZE_STD_1 && user_lastdatabase_size <= SMARTSSD_DATABASE_SIZE_STD_0)
		user_ssd2fpga_effbw = SMARTSSD_SSD2FPGA_EFFBW_1*user_lastdatabase_size/SMARTSSD_DATABASE_SIZE_STD_1;
	else
		user_ssd2fpga_effbw = SMARTSSD_SSD2FPGA_EFFBW_0;

	double host_total_ssd2fpga_latency = 0;
	for(int i=0; i<host_iteration+1; i++) {
		if(i==host_iteration)
			host_total_ssd2fpga_latency = host_total_ssd2fpga_latency +	(user_lastdatabase_size/user_ssd2fpga_effbw)*1000;
		else
			host_total_ssd2fpga_latency = host_total_ssd2fpga_latency + ((double)UNIT_DATABASE_SIZE*2/SMARTSSD_SSD2FPGA_EFFBW_0)*1000;
	}
	
	// Data transfer time (HOST2FPGA) time expectation
	size_t user_outbuffer_size;
	if(user_query == Q3 || user_query == Q4 || user_query == Q7 || user_query == Q8)
		user_outbuffer_size = 4096;
	else
		user_outbuffer_size = (user_pagenum-host_iteration*131072*2)*4096/2;

	double user_fpga2host_effbw;
	if(user_outbuffer_size <= SMARTSSD_OUTBUF_SIZE_STD_1)
		user_fpga2host_effbw = SMARTSSD_FPGA2HOST_EFFBW_1;
	else if(user_outbuffer_size > SMARTSSD_OUTBUF_SIZE_STD_1 && user_outbuffer_size <= SMARTSSD_OUTBUF_SIZE_STD_0)
		user_fpga2host_effbw = SMARTSSD_FPGA2HOST_EFFBW_1*user_outbuffer_size/SMARTSSD_OUTBUF_SIZE_STD_1;
	else
		user_fpga2host_effbw = SMARTSSD_FPGA2HOST_EFFBW_0;

	double host_total_fpga2host_latency = 0;
	if(user_query == Q3 || user_query == Q4 || user_query == Q7 || user_query == Q8) {
		for(int i=0; i<host_iteration+1; i++) {
			host_total_fpga2host_latency = host_total_fpga2host_latency + (user_outbuffer_size/user_fpga2host_effbw)*1000;
		}
	}
	else {
		for(int i=0; i<host_iteration+1; i++) {
			if(i==host_iteration)
				host_total_fpga2host_latency = host_total_fpga2host_latency + (user_outbuffer_size/user_fpga2host_effbw)*1000;
			else
				host_total_fpga2host_latency = host_total_fpga2host_latency + ((131072*4096)/SMARTSSD_FPGA2HOST_EFFBW_0)*1000;
		}
	}

	// Kernel compute time expectation
	size_t user_unit_com_cycle = 0;
	size_t user_unit_dma_cycle = 0;
	
	if (user_dataset == HIGGS){
		switch (user_query_num){
			case (Q1):
				user_unit_com_cycle = 5522;
				user_unit_dma_cycle = 703;
				break;
			case (Q2):
				user_unit_com_cycle = 5522;
				user_unit_dma_cycle = 703;
				break;
			case (Q3):
				user_unit_com_cycle = 5582;
				user_unit_dma_cycle = 518;
				break;
			case (Q4):
				user_unit_com_cycle = 5582;
				user_unit_dma_cycle = 518;
				break;
			case (Q5):
				user_unit_com_cycle = 5552;
				user_unit_dma_cycle = 701;
				break;
			case (Q6):
				user_unit_com_cycle = 5552;
				user_unit_dma_cycle = 701;
				break;
			case (Q7):
				user_unit_com_cycle = 5612;
				user_unit_dma_cycle = 521;
				break;
			case (Q8):
				user_unit_com_cycle = 5612;
				user_unit_dma_cycle = 521;
				break;
			case (Q9):
				user_unit_com_cycle = 5522;
				user_unit_dma_cycle = 703;
				break;
			case (Q10):
				user_unit_com_cycle = 28048;
				user_unit_dma_cycle = 5766;
				break;
			case (Q11):
				user_unit_com_cycle = 4591;
				user_unit_dma_cycle = 5534;
				break;
			default:
				printf("undifined query\n");
		}
	} else if (user_dataset == FOREST){
		switch (user_query_num){
			case (Q1):
				user_unit_com_cycle = 5215;
				user_unit_dma_cycle = 785;
				break;
			case (Q2):
				user_unit_com_cycle = 5215;
				user_unit_dma_cycle = 778503;
				break;
			case (Q3):
				user_unit_com_cycle = 5308;
				user_unit_dma_cycle = 527;
				break;
			case (Q4):
				user_unit_com_cycle = 5308;
				user_unit_dma_cycle = 527;
				break;
			case (Q5):
				user_unit_com_cycle = 5244;
				user_unit_dma_cycle = 782;
				break;
			case (Q6):
				user_unit_com_cycle = 5244;
				user_unit_dma_cycle = 782;
				break;
			case (Q7):
				user_unit_com_cycle = 5338;
				user_unit_dma_cycle = 535;
				break;
			case (Q8):
				user_unit_com_cycle = 5338;
				user_unit_dma_cycle = 535;
				break;
			case (Q9):
				user_unit_com_cycle = 5215;
				user_unit_dma_cycle = 785;
				break;
			case (Q10):
				user_unit_com_cycle = 14651;
				user_unit_dma_cycle = 5685;
				break;
			case (Q11):
				user_unit_com_cycle = 2903;
				user_unit_dma_cycle = 5500;
				break;
			default:
				printf("undifined query\n");
		}
	} else if (user_dataset == WILT){
		switch (user_query_num){
			case (Q1):
				user_unit_com_cycle = 5087;
				user_unit_dma_cycle = 884;
				break;
			case (Q2):
				user_unit_com_cycle = 5087;
				user_unit_dma_cycle = 884;
				break;
			case (Q3):
				user_unit_com_cycle = 5238;
				user_unit_dma_cycle = 536;
				break;
			case (Q4):
				user_unit_com_cycle = 5238;
				user_unit_dma_cycle = 536;
				break;
			case (Q5):
				user_unit_com_cycle = 5117;
				user_unit_dma_cycle = 882;
				break;
			case (Q6):
				user_unit_com_cycle = 5117;
				user_unit_dma_cycle = 882;
				break;
			case (Q7):
				user_unit_com_cycle = 5268;
				user_unit_dma_cycle = 534;
				break;
			case (Q8):
				user_unit_com_cycle = 5268;
				user_unit_dma_cycle = 534;
				break;
			case (Q9):
				user_unit_com_cycle = 5087;
				user_unit_dma_cycle = 882;
				break;
			case (Q10):
				user_unit_com_cycle = 7785;
				user_unit_dma_cycle = 5864;
				break;
			case (Q11):
				user_unit_com_cycle = 4512;
				user_unit_dma_cycle = 5623;
				break;
			default:
				printf("undifined query\n");
		}
	} else if (user_dataset == HABERMAN){
		switch (user_query_num){
			case (Q1):
				user_unit_com_cycle = 4335;
				user_unit_dma_cycle = 980;
				break;
			case (Q2):
				user_unit_com_cycle = 4335;
				user_unit_dma_cycle = 980;
				break;
			case (Q3):
				user_unit_com_cycle = 4507;
				user_unit_dma_cycle = 533;
				break;
			case (Q4):
				user_unit_com_cycle = 4507;
				user_unit_dma_cycle = 533;
				break;
			case (Q5):
				user_unit_com_cycle = 4365;
				user_unit_dma_cycle = 949;
				break;
			case (Q6):
				user_unit_com_cycle = 4365;
				user_unit_dma_cycle = 949;
				break;
			case (Q7):
				user_unit_com_cycle = 4537;
				user_unit_dma_cycle = 534;
				break;
			case (Q8):
				user_unit_com_cycle = 4537;
				user_unit_dma_cycle = 534;
				break;
			case (Q9):
				user_unit_com_cycle = 4335;
				user_unit_dma_cycle = 979;
				break;
			case (Q10):
				user_unit_com_cycle = 4019;
				user_unit_dma_cycle = 5356;
				break;
			case (Q11):
				user_unit_com_cycle = 4153;
				user_unit_dma_cycle = 5050;
				break;
			default:
				printf("undifined query\n");
		}
	} else{
		printf("undifined dataset\n");
	}

	const size_t user_clock = USER_CLOCK;

	size_t user_total_com_cycle = 0;
	for(int i=0; i<host_iteration+1; i++) {
		if(i==host_iteration)
			user_total_com_cycle = user_total_com_cycle + user_unit_com_cycle*page_iteration;
		else
			user_total_com_cycle = user_total_com_cycle + user_unit_com_cycle*((long long)UNIT_DATABASE_SIZE*2)/PAGE_SIZE;
	}

	size_t user_total_dma_cycle = 0;
	if(user_query==Q3||user_query==Q4||user_query==Q7||user_query==Q8)
		user_total_dma_cycle = (host_iteration+1)*user_unit_dma_cycle;
	else {
		for(int i=0; i<host_iteration+1; i++) {
			if(i==host_iteration)
				user_total_dma_cycle = user_total_dma_cycle + user_unit_dma_cycle*page_iteration;
			else
				user_total_dma_cycle = user_total_dma_cycle + user_unit_dma_cycle*((long long)UNIT_DATABASE_SIZE*2)/PAGE_SIZE;
		}
	}

	size_t user_effective_com_cycle = user_total_com_cycle/user_corenum;
	size_t user_effective_dma_cycle = user_total_dma_cycle/user_corenum;

	double user_total_com_latency = ((double)user_effective_com_cycle/((double)user_clock*1000000))*1000;					
	double user_total_dma_latency  = ((double)user_effective_dma_cycle/((double)user_clock*1000000))*1000;
	double user_total_kernel_latency = user_total_com_latency + user_total_dma_latency;

	double user_kernel_overhead_latency = user_total_kernel_latency*0.041;

	double user_total_latency = host_total_createbuffer_latency+host_total_addressmap_latency+host_total_ssd2fpga_latency+host_total_setkernel_latency+user_total_kernel_latency+user_kernel_overhead_latency+host_total_fpga2host_latency;

	return user_total_latency;
}

static void
sw_stack_for_hw(const char* query_string, List* querytrees){
	
	int query_length = strlen(query_string);
	char* query_str = (char*)malloc(sizeof(char) * (query_length + 1));
	strcpy(query_str, query_string);

	int word_size = 0;
	char** word_array = (char**)malloc(sizeof(char *) * (query_length + 1));

    char* word_tmp;
    word_tmp = strtok(query_str, " ,()[];\n'");
	while (word_tmp != NULL) {
        word_array[word_size] = (char *)malloc(sizeof(char) * 25);
		strcpy(word_array[word_size], word_tmp);
		word_size++;
		word_tmp = strtok(NULL, " ,()[];\n'");
	}
	// extra check for train phase (tree)
	for (int i = 0 ; i < word_size ; i++){
		if (hw_strcmp(word_array[i], (char*)"madlib.tree_train")){
			//printf("train found -> setting flag\n");
			train_flag = true;
			tree_table_name = (char *)malloc(sizeof(char) * 100);
			strcpy(tree_table_name, word_array[3]);
			//printf("trage table = %s\n", tree_table_name);
		}
	}

	// extrack HW operation information
	struct operation_info op_info;
	init_operation_info(&op_info);
	extract_operation_info(word_array, word_size, &op_info);
	printf_op_info(op_info);
	
	free(query_str);
	for (int word_arr_cnt = 0 ; word_arr_cnt < word_size ; word_arr_cnt++){
		free(word_array[word_arr_cnt]);
	}
	free(word_array);

	// hw support operation
	if (op_info.hw_support){
		printf("hw supported\n");
		op_info.hw_query_num = get_query_num(op_info);
		query_num_recorded = true;
		query_num = op_info.hw_query_num;
		// get oids and size of data and model table
		char* data_model_query = (char*)malloc(sizeof(char) * (20 + strlen(op_info.data_table_name) + strlen(op_info.model_table_name)));
		hw_query_modification(op_info.data_table_name, op_info.model_table_name, data_model_query);
		
		List* data_model_parsetree_list;
		ListCell* data_model_parsetree_item;
		List* data_model_querytree_list;
		data_model_parsetree_list = pg_parse_query(data_model_query);
		foreach(data_model_parsetree_item, data_model_parsetree_list) {
			RawStmt* parsetree_modified = lfirst_node(RawStmt, data_model_parsetree_item);
			data_model_querytree_list = pg_analyze_and_rewrite(parsetree_modified, data_model_query, NULL, 0, NULL);
			//printf("-----------------------------------please1... %d\n", ((FetchStmt *)parsetree_modified->stmt)->howMany);
		}
		free(data_model_query);
		
		int rtable_num = 0;
		int* rtable_id;
		int* rtable_relid;
		char** rtable_name;
		int* rtable_colnum;
		unsigned long long int* rtable_colsel;
		char*** rtable_colname;
		int query_num_local = 0;
		int* table_size;
		// 0th: data table, 1th: data table
		ListCell* query_list;
		foreach(query_list, data_model_querytree_list) {
			Query* query = lfirst_node(Query, query_list);
			query_num_local++;
			rtable_num = list_length(query->rtable);
			rtable_id = (int*)malloc(sizeof(int) * rtable_num);
			rtable_relid = (int*)malloc(sizeof(int) * rtable_num);
			rtable_name = (char**)malloc(sizeof(char *) * rtable_num);
			rtable_colnum = (int*)malloc(sizeof(int) * rtable_num);
			rtable_colsel = (unsigned long long int *)malloc(sizeof(unsigned long long int) * rtable_num);
			rtable_colname = (char***)malloc(sizeof(char**) * rtable_num);
			table_size = (int*)malloc(sizeof(int) * rtable_num);
			hw_rtable_extract(query, rtable_id, rtable_relid, rtable_name, rtable_colnum, rtable_colsel, rtable_colname, table_size);
		}
		
		printf("hw stack debug - data check\n");
		for (int k = 0 ; k < rtable_num ; k++){
			printf("-- %dth --\nrtable_id: %d\nrtable_relid: %d\nrtable_name: %s\nrtable_colnum: %d\nrtable_colsel: %lld\ntable_size: %d\n",
												k, *(rtable_id + k), *(rtable_relid + k), *(rtable_name + k), *(rtable_colnum + k), *(rtable_colsel + k),
												*(table_size + k));
		}
		
		// get additional information for specific cases
		if ((op_info.hw_operation == LINREGR) | (op_info.hw_operation == LOGREGR)){

			//int model_col_num;
			//for (int now_model_num = 0 ; now_model_num < rtable_colnum[1] ; now_model_num++){
			//	if (hw_strcmp(op_info.model_col_name, rtable_colname[1][now_model_num])){
			//		model_col_num = now_model_num;
			//		break;
			//	}
			//}
			//printf("model col num: %d\n", model_col_num);

    		uint32_t mask_base = 0 | 1;

			int* model_col_num = (int *)malloc(sizeof(int) * op_info.model_col_len);
			uint32_t model_col_num_bit = 0;
			for (int model_num = 0 ; model_num < op_info.model_col_len ; model_num++){
				char* now_col_name = op_info.model_col_name[model_num];
				if (hw_strcmp(now_col_name, (char*)"1")){
					model_col_num[model_num] = -1; // bias
				} else{
					for (int now_col_num = 0 ; now_col_num < rtable_colnum[1] ; now_col_num++){
						if (hw_strcmp(now_col_name, rtable_colname[1][now_col_num])){
							model_col_num[model_num] = now_col_num;
							model_col_num_bit |= (mask_base << (31 - now_col_num));
							continue;
						}
					}
				}
			}

			printf("(LINREGR/LOGREGR)model col nums: ");
			for (int i = 0 ; i < op_info.model_col_len ; i++){
				printf("[%d] ", model_col_num[i]);
			}
			printf("\n");
			printf("(LINREGR/LOGREGR)model col nums (bitwise): ");	
			for (int l = 31; l >= 0; --l) {
				int result = model_col_num_bit >> l & 0x1;
				printf("%d", result);
			}
			printf("\n");
			free(model_col_num);

			int* data_col_num = (int *)malloc(sizeof(int) * op_info.data_col_len);
			uint32_t data_col_num_bit = 0;
			for (int data_num = 0 ; data_num < op_info.data_col_len ; data_num++){
				char* now_col_name = op_info.data_col_name[data_num];
				if (hw_strcmp(now_col_name, (char*)"1")){
					data_col_num[data_num] = -1; // bias
				} else{
					for (int now_col_num = 0 ; now_col_num < rtable_colnum[0] ; now_col_num++){
						if (hw_strcmp(now_col_name, rtable_colname[0][now_col_num])){
							data_col_num[data_num] = now_col_num;
							data_col_num_bit |= (mask_base << (31 - now_col_num));
							continue;
						}
					}
				}
			}

			printf("(LINREGR/LOGREGR)data col nums: ");
			for (int i = 0 ; i < op_info.data_col_len ; i++){
				printf("[%d] ", data_col_num[i]);
			}
			printf("\n");
			printf("(LINREGR/LOGREGR)data col nums (bitwise): ");	
			for (int l = 31; l >= 0; --l) {
				int result = data_col_num_bit >> l & 0x1;
				printf("%d", result);
			}
			printf("\n");
			free(data_col_num);

		} else if ((op_info.hw_operation == SVM) | (op_info.hw_operation == MLP) | (op_info.hw_operation == TREE)){
			if ((op_info.hw_operation == SVM) | (op_info.hw_operation == MLP)){
				int data_col_num;
				for (int now_data_num = 0 ; now_data_num < rtable_colnum[0] ; now_data_num++){
					if (hw_strcmp(op_info.id_col_name, rtable_colname[0][now_data_num])){
						data_col_num = now_data_num;
						break;
					}
				}
				printf("(SVM/MLP)model col num: %d\n", data_col_num);
			}

		} else {
			printf("operation is not supported in this hw\n");
			free_operation_info(&op_info);
			return;
		}

		// get additional information for filtering if needed
		if (op_info.filter_flag){
			printf("filter phase\n");
			if (hw_strcmp(op_info.filter_table_name, op_info.data_table_name)){ // data table = filter table
				int filter_col_num;
				for (int now_filter_col = 0 ; now_filter_col < rtable_colnum[0] ; now_filter_col++){
					if (hw_strcmp(op_info.filter_col_name, rtable_colname[0][now_filter_col])){
						filter_col_num = now_filter_col;
						break;
					}
				}
				printf("filter col num: %d\n", filter_col_num);
			} else{
				printf("indefined filter operation");
			}
		}

		// get additional information for aggregation if needed
		if (op_info.aggr_flag){
			printf("aggr phase\n");
		}
		
		// Predictor
		// Cost approx function
		double page_num;
		double new_data_num = get_data_num(rtable_relid[0], table_size[0], &page_num);
		printf("Extracted data num: %f\n", new_data_num);
		num_rows_recorded = true;
		num_rows = new_data_num;
		
		double new_exec_time_predict = 0;
		double new_data_num_predict = new_data_num / 1000;
		
		if (USE_ADAPTIVE_RANGE){
			if ((data1_len[query_num] > ADJ_MIN_DATANUM) & (data2_len[query_num] > ADJ_MIN_DATANUM) & (data3_len[query_num] > ADJ_MIN_DATANUM)){
				printf("\t-------HW predictor debugging-------\n\t");
				// CPU COST APPROXIMATION
				if (new_data_num_predict <= data_num2[query_num][0]){
					new_exec_time_predict = polyval(new_data_num_predict, exec_coef1[query_num]);
				} else if (new_data_num_predict <= data_num3[query_num][0]){
					new_exec_time_predict = polyval(new_data_num_predict, exec_coef2[query_num]);
				} else{
					new_exec_time_predict = polyval(new_data_num_predict, exec_coef3[query_num]);
				}	
				printf("CPU cost prediction result [datanum: %f -> prediction time: %.3f (ms)]\n\t", new_data_num, new_exec_time_predict);

				// HW COST APPROXIMATION
				int dataset_num = -1;
				if (op_info.data_col_len > 17){ // HIGGS
					dataset_num = HIGGS;
				} else if (op_info.data_col_len > 8){ // FOREST
					dataset_num = FOREST;
				} else if (op_info.data_col_len > 4){ // WILT
					dataset_num = WILT;
				} else{ // HABERMAN
					dataset_num = HABERMAN;
				}

				double hw_expectation_time = get_hw_expectation_time(query_num, dataset_num, page_num);
				printf("HW cost prediction result [datanum(%s): %f -> prediction time: %.3f (ms)]\n\t", new_data_num, 
													(dataset_num == HIGGS) ? ("HIGGS") : ((dataset_num == FOREST) ? ("FOREST") : ((dataset_num == WILT) ? ("WILT") : 
													(dataset_num == HABERMAN) ? ("HABERMAN") : ("ERROR"))), hw_expectation_time);
				
				if (new_exec_time_predict < hw_expectation_time){
					printf("CPU time is %.3f times faster -> use CPU (CPU/HW ratio = %.3f)\n\t", hw_expectation_time/new_exec_time_predict, new_exec_time_predict/hw_expectation_time);
				} else{
					printf("HW time is %.3f times faster -> use HW (CPU/HW ratio = %.3f)\n\t", new_exec_time_predict/hw_expectation_time, new_exec_time_predict/hw_expectation_time);
				}
				printf("--------------------------------------\n");
			} else{
				printf("CPU cost prediction -> not enough data gathered\n");
			}
		}
		
		free_operation_info(&op_info);
		free(rtable_id);
		free(rtable_relid);
		for (int free_rtable_name = 0 ; free_rtable_name < rtable_num ; free_rtable_name++){
			free(rtable_name[free_rtable_name]);
		}
		free(rtable_name);
		free(rtable_colnum);
		free(rtable_colsel);
		for (int query_cnt = 0 ; query_cnt < query_num_local ; query_cnt++){
			for (int free_rtable_colsel = 0 ; free_rtable_colsel < rtable_num ; free_rtable_colsel++){
				free(rtable_colname[query_cnt][free_rtable_colsel]);
			}
			free(rtable_colname[query_cnt]);
		}
		free(rtable_colname);
		return;
	} else{ // hw does not support operation
		free_operation_info(&op_info);
		return;
	}
}

// adaptive range functionality

int polyfit(int pointCount, double *xValues, double *yValues, int coefficientCount, double *coefficientResults){

    int rVal = 0;
    int degree = coefficientCount - 1;

    // Check that the input pointers aren't null.
    if ((NULL == xValues) || (NULL == yValues) || (NULL == coefficientResults)){
        return -1;
    }
    // Check that pointCount >= coefficientCount.
    if (pointCount < coefficientCount){
        return -2;
    }

    // Make the A matrix:
    matrix_t *pMatA = createMatrix(pointCount, coefficientCount);
    if (NULL == pMatA){
        return -3;
    }
    for (int r = 0; r < pointCount; r++){
        for (int c = 0; c < coefficientCount; c++){
            *(MATRIX_VALUE_PTR(pMatA, r, c)) = pow((xValues[r]), (double) (degree -c));
        }
    }

    // Make the b matrix
    matrix_t *pMatB = createMatrix(pointCount, 1);
    if (NULL == pMatB){
        return -3;
    }

    for (int r = 0; r < pointCount; r++){
        *(MATRIX_VALUE_PTR(pMatB, r, 0)) = yValues[r];
    }

    // Make the transpose of matrix A
    matrix_t * pMatAT = createTranspose(pMatA);
    if (NULL == pMatAT){
        return -3;
    }

    // Make the product of matrices AT and A:
    matrix_t *pMatATA = createProduct(pMatAT, pMatA);
    if (NULL == pMatATA){
        return -3;
    }

    // Make the product of matrices AT and b:
    matrix_t *pMatATB = createProduct(pMatAT, pMatB);
    if (NULL == pMatATB){
        return -3;
    }

    // Now we need to solve the system of linear equations,
    // (AT)Ax = (AT)b for "x", the coefficients of the polynomial.

    for (int c = 0; c < pMatATA->cols; c++){
        int pr = c;     // pr is the pivot row.
        double prVal = *MATRIX_VALUE_PTR(pMatATA, pr, c);
        // If it's zero, we can't solve the equations.
        if (prVal == 0.0){
            // printf( "Unable to solve equations, pr = %d, c = %d.\n", pr, c );
            rVal = -4;
            break;
        }
        for (int r = 0; r < pMatATA->rows; r++){
            if (r != pr){
                double targetRowVal = *MATRIX_VALUE_PTR(pMatATA, r, c);
                double factor = targetRowVal / prVal;
                for (int c2 = 0; c2 < pMatATA->cols; c2++){
                    *MATRIX_VALUE_PTR(pMatATA, r, c2) -=  *MATRIX_VALUE_PTR(pMatATA, pr, c2) * factor; 
                }
                *MATRIX_VALUE_PTR(pMatATB, r, 0) -=  *MATRIX_VALUE_PTR(pMatATB, pr, 0) * factor;
            }
        }
    }
    for (int c = 0; c < pMatATA->cols; c++){
        int pr = c;
        // now, pr is the pivot row.
        double prVal = *MATRIX_VALUE_PTR(pMatATA, pr, c);
        *MATRIX_VALUE_PTR(pMatATA, pr, c) /= prVal;
        *MATRIX_VALUE_PTR(pMatATB, pr, 0) /= prVal;
    }

    for(int i = 0; i < coefficientCount; i++){
        coefficientResults[i] = *MATRIX_VALUE_PTR(pMatATB, i, 0);
    }

    destroyMatrix(pMatATB);
    destroyMatrix(pMatATA);
    destroyMatrix(pMatAT);

    destroyMatrix(pMatA);
    destroyMatrix(pMatB);

    return rVal;
}

double *polyval_multi(double* data_num, double* exec_time, int data_len, double* exec_coef){

    //printf("polyval\n");
    double *result = (double *)malloc(sizeof(double) * data_len);
    double partial_result = 0;
    double now_data = 0; 
    double partial_mul = 0;
    for (int i = 0 ; i < data_len ; i++){
        partial_result = 0;
        now_data = data_num[i];
        for (int j = EXEC_ORDER ; j >= 0 ; j--){ // 3 2 1 0
            partial_mul = 1;
            for (int k = 0 ; k < j ; k++){
                partial_mul *= now_data;
            }
            partial_result += exec_coef[EXEC_ORDER - j] * partial_mul;
        }
        result[i] = partial_result;
        //printf("%lf\n", partial_result);
    }
    return result;
}

double polyval(double new_data, double* exec_coef){
    double result = 0;
    double now_data = new_data; 
    double partial_mul = 0;
    
    for (int j = EXEC_ORDER ; j >= 0 ; j--){ // 3 2 1 0
        partial_mul = 1;
        for (int k = 0 ; k < j ; k++){
            partial_mul *= now_data;
        }
        result += exec_coef[EXEC_ORDER - j] * partial_mul;
    }
    return result;
}

static matrix_t *createTranspose(matrix_t *pMat){
    matrix_t *rVal = (matrix_t *) calloc(1, sizeof(matrix_t));
    rVal->pContents = (double *) calloc( pMat->rows * pMat->cols, sizeof(double));
    rVal->cols = pMat->rows;
    rVal->rows = pMat->cols;
    for (int r = 0; r < rVal->rows; r++){
        for(int c = 0; c < rVal->cols; c++){
            *MATRIX_VALUE_PTR(rVal, r, c) = *MATRIX_VALUE_PTR(pMat, c, r);
        }
    }
    return rVal;
}

static matrix_t *createProduct(matrix_t *pLeft, matrix_t *pRight){
    matrix_t *rVal = NULL;
    if((NULL == pLeft) || (NULL == pRight) || (pLeft->cols != pRight->rows)){
        printf("Illegal parameter passed to createProduct().\n");
    } else{
        // Allocate the product matrix.
        rVal = (matrix_t *) calloc(1, sizeof(matrix_t));
        rVal->rows = pLeft->rows;
        rVal->cols = pRight->cols;
        rVal->pContents = (double *) calloc(rVal->rows * rVal->cols, sizeof(double));

        // Initialize the product matrix contents:
        // product[i,j] = sum{k = 0 .. (pLeft->cols - 1)} (pLeft[i,k] * pRight[ k, j])
        for (int i = 0; i < rVal->rows; i++){
            for (int j = 0; j < rVal->cols; j++){
                for (int k = 0; k < pLeft->cols; k++){
                    *MATRIX_VALUE_PTR(rVal, i, j) += (*MATRIX_VALUE_PTR(pLeft, i, k)) * (*MATRIX_VALUE_PTR(pRight, k, j));
                }
            }
        }
    }      
    return rVal;
}

static void destroyMatrix(matrix_t *pMat){
    if (NULL != pMat){
        if (NULL != pMat->pContents){
            free(pMat->pContents);
        }
        free(pMat);
    }
}

static matrix_t *createMatrix(int rows, int cols){  
    matrix_t *rVal = (matrix_t *) calloc(1, sizeof(matrix_t));
    if (NULL != rVal){
        rVal->rows = rows;
        rVal->cols = cols;
        rVal->pContents = (double *) calloc(rows * cols, sizeof(double));
        if (NULL == rVal->pContents){
            free(rVal);
            rVal = NULL;
        }
    }
    return rVal;
}

void print_data(double* data, int data_len){
    for (int i = 0 ; i < data_len ; i++){
        /*if ((i % 10 == 0) & (i != 0)){
            printf("\n");
        }*/
        printf("%lf ", data[i]);
    }
    printf("\n");
}

int get_avg_error(double* data_num, double* exec_time, int data_len, double* error, double* error_rate, double* exec_coef, bool first_flag){

    //printf("get_avg_error\n");
    //print_data(data_num, data_len);
    //print_data(exec_time, data_len);
    if (polyfit(data_len, data_num, exec_time, EXEC_ORDER + 1, exec_coef)){
        printf("Error occured in polyfit\n");
    }
    /*
    for (int i = 0 ; i <= EXEC_ORDER ; i++){
        printf("%e\n", exec_coef[i]);
    }
    */
    double *assume_result = polyval_multi(data_num, exec_time, data_len, exec_coef);
    /*
    for (int i = 0 ; i < data_len ; i++){
        printf("%lf ", assume_result[i]);
    }
    printf("\n");
    */
    double partial_error = 0;
    double total_error = 0;
    double total_error_rate = 0;
    for (int j = 0 ; j < data_len ; j++){
        partial_error = ABS(exec_time[j] - assume_result[j]);
        if ((!first_flag) & (j == 0)){
            continue;
        }
        total_error += partial_error;
        total_error_rate += ((partial_error / exec_time[j]) * 100);
    }
    *error = total_error / data_len;
    *error_rate = total_error_rate / data_len;
    //printf("error: %lf, error_rate: %lf\n", *error, *error_rate);
    free(assume_result);
    
    return 0;
}

int adjust_range(double* data_num1, double* data_num2, double* exec_time1, double* exec_time2, int* data1_len, int* data2_len,
                 double** min_left_data_num, double** min_right_data_num, 
                 double** min_left_exec_time, double** min_right_exec_time, 
                 double** min_left_coef, double** min_right_coef, bool first_flag){
    
    //printf("adjust_range\n");
    //print_data(data_num1, *data1_len);
    //print_data(exec_time1, *data1_len);

    int def_data1_len = *data1_len;
    int def_data2_len = *data2_len;

    if ((def_data1_len < 3) | (def_data2_len < 3)){
        printf("too small data for range - break");
    }

    double def_left_error = 0;
    double *def_left_coef = (double *)malloc(sizeof(double) * (EXEC_ORDER + 1));
    double def_left_error_rate = 0;
    double def_right_error = 0;
    double *def_right_coef = (double *)malloc(sizeof(double) * (EXEC_ORDER + 1));
    double def_right_error_rate = 0;

    if (get_avg_error(data_num1, exec_time1, def_data1_len, &def_left_error, &def_left_error_rate, def_left_coef, first_flag)){
        printf("Error occured in get_avg_error\n");
    }
    //printf("[left] error: %lf, error_rate: %lf\n", def_left_error, def_left_error_rate);
    if (get_avg_error(data_num2, exec_time2, def_data2_len, &def_right_error, &def_right_error_rate, def_right_coef, false)){
        printf("Error occured in get_avg_error\n");
    }
    //printf("[right] error: %lf, error_rate: %lf\n", def_right_error, def_right_error_rate);
    //printf("[left] error_rate: %lf [right] error_rate: %lf\n", def_left_error_rate, def_right_error_rate);

    //print_data(data_num1, def_data1_len);
    //print_data(data_num2, def_data2_len);

    double left_error;
    double left_error_rate;
    double right_error;
    double right_error_rate;

    // phase 1 (left moving phase)
    //printf("Phase 1\n");
    double min_left_error_1 = def_left_error;
    double min_right_error_1 = def_right_error;
    double min_left_error_rate_1 = def_left_error_rate;
    double min_right_error_rate_1 = def_right_error_rate;    
    
    double *min_left_coef_1 = (double *)malloc(sizeof(double) * (EXEC_ORDER + 1));
    double *min_right_coef_1 = (double *)malloc(sizeof(double) * (EXEC_ORDER + 1));
    for (int coef_i = 0 ; coef_i < EXEC_ORDER + 1 ; coef_i++){
        min_left_coef_1[coef_i] = def_left_coef[coef_i];
        min_right_coef_1[coef_i] = def_right_coef[coef_i];
    }
    int min_left_len_1 = def_data1_len;
    int min_right_len_1 = def_data2_len;

    int total_len = def_data1_len + def_data2_len;
    double *min_left_data_num_1 = (double *)malloc(sizeof(double) * total_len);
    double *min_right_data_num_1 = (double *)malloc(sizeof(double) * total_len);
    double *min_left_exec_time_1 = (double *)malloc(sizeof(double) * total_len);
    double *min_right_exec_time_1 = (double *)malloc(sizeof(double) * total_len);

    for (int left_i = 0 ; left_i < def_data1_len ; left_i++){
        min_left_data_num_1[left_i] = data_num1[left_i];
        min_left_exec_time_1[left_i] = exec_time1[left_i];
    }
    for (int right_i = 0 ; right_i < def_data2_len ; right_i++){
        min_right_data_num_1[right_i] = data_num2[right_i];
        min_right_exec_time_1[right_i] = exec_time2[right_i];
    }

    int left_len_1 = def_data1_len;
    int right_len_1 = def_data2_len;

    for (int phase1_rec = 0 ; phase1_rec < def_data2_len ; phase1_rec++){
        min_left_data_num_1[left_len_1] = min_right_data_num_1[1];
        min_left_exec_time_1[left_len_1] = min_right_exec_time_1[1];
        left_len_1 += 1;
        for (int right_delete = 0 ; right_delete < (right_len_1 - 1) ; right_delete++){
            min_right_data_num_1[right_delete] = min_right_data_num_1[right_delete + 1];
            min_right_exec_time_1[right_delete] = min_right_exec_time_1[right_delete + 1];
        }
        min_right_data_num_1[(right_len_1 - 1)] = 0;
        min_right_exec_time_1[(right_len_1 - 1)] = 0;
        right_len_1 -= 1;

        //print_data(min_left_data_num_1, left_len_1);
        //print_data(min_right_data_num_1, right_len_1);

        double *left_coef_1 = (double *)malloc(sizeof(double) * (EXEC_ORDER + 1));
        if (get_avg_error(min_left_data_num_1, min_left_exec_time_1, left_len_1, &left_error, &left_error_rate, left_coef_1, first_flag)){
            printf("Error occured in get_avg_error\n");
        }
        double *right_coef_1 = (double *)malloc(sizeof(double) * (EXEC_ORDER + 1));
        if (get_avg_error(min_right_data_num_1, min_right_exec_time_1, right_len_1, &right_error, &right_error_rate, right_coef_1, false)){
            printf("Error occured in get_avg_error\n");
        }     
        //printf("[left] error_rate: %lf [right] error_rate: %lf\n", left_error_rate, right_error_rate);

        if ((left_error_rate < min_left_error_rate_1) & (right_error_rate < min_right_error_rate_1)){
            //printf("case 1\n");
            //printf("updated to %lf, %lf\n", left_error_rate, right_error_rate);
            min_left_error_1 = left_error;
            min_right_error_1 = right_error;
            min_left_error_rate_1 = left_error_rate;
            min_right_error_rate_1 = right_error_rate;
            free(min_left_coef_1);
            free(min_right_coef_1);
            min_left_coef_1 = left_coef_1;
            min_right_coef_1 = right_coef_1;
            min_left_len_1 = left_len_1;
            min_right_len_1 = right_len_1;
        } else if ((left_error_rate > min_left_error_rate_1) & (right_error_rate > min_right_error_rate_1)){
            //printf("case 2\n");
            //printf("break\n");
            // Roll back 
            for (int right_delete = right_len_1 ; right_delete >= 1 ; right_delete--){
                min_right_data_num_1[right_delete] = min_right_data_num_1[right_delete - 1];
                min_right_exec_time_1[right_delete] = min_right_exec_time_1[right_delete - 1];
            }
            min_right_data_num_1[0] = min_left_data_num_1[(left_len_1 - 2)];
            min_right_exec_time_1[0] = min_left_exec_time_1[(left_len_1 - 2)];
            right_len_1 += 1;
            min_left_data_num_1[(left_len_1 - 1)] = 0;
            min_left_exec_time_1[(left_len_1 - 1)] = 0;
            left_len_1 -= 1;
            free(left_coef_1);
            free(right_coef_1);
            break;
        } else{
            if ((left_error_rate < min_left_error_rate_1) & (right_error_rate > min_right_error_rate_1)){
                //printf("case 3_1\n");
                double left_improved = min_left_error_rate_1 - left_error_rate;
                double right_worsed = right_error_rate - min_right_error_rate_1;
                if (left_improved > right_worsed){
                    //printf("updated to %lf, %lf\n", left_error_rate, right_error_rate);
                    min_left_error_1 = left_error;
                    min_right_error_1 = right_error;
                    min_left_error_rate_1 = left_error_rate;
                    min_right_error_rate_1 = right_error_rate;
                    free(min_left_coef_1);
                    free(min_right_coef_1);
                    min_left_coef_1 = left_coef_1;
                    min_right_coef_1 = right_coef_1;
                    min_left_len_1 = left_len_1;
                    min_right_len_1 = right_len_1;
                } else{
                    //printf("break\n");
                    // Roll back 
                    for (int right_delete = right_len_1 ; right_delete >= 1 ; right_delete--){
                        min_right_data_num_1[right_delete] = min_right_data_num_1[right_delete - 1];
                        min_right_exec_time_1[right_delete] = min_right_exec_time_1[right_delete - 1];
                    }
                    min_right_data_num_1[0] = min_left_data_num_1[(left_len_1 - 2)];
                    min_right_exec_time_1[0] = min_left_exec_time_1[(left_len_1 - 2)];
                    right_len_1 += 1;
                    min_left_data_num_1[(left_len_1 - 1)] = 0;
                    min_left_exec_time_1[(left_len_1 - 1)] = 0;
                    left_len_1 -= 1;
                    free(left_coef_1);
                    free(right_coef_1);
                    break;
                }
            } else{
                //printf("case 3_2\n");
                double left_worsed = left_error_rate - min_left_error_rate_1;
                double right_improved = min_right_error_rate_1 - right_error_rate;
                if (right_improved > left_worsed){
                    //printf("updated to %lf, %lf\n", left_error_rate, right_error_rate);
                    min_left_error_1 = left_error;
                    min_right_error_1 = right_error;
                    min_left_error_rate_1 = left_error_rate;
                    min_right_error_rate_1 = right_error_rate;
                    free(min_left_coef_1);
                    free(min_right_coef_1);
                    min_left_coef_1 = left_coef_1;
                    min_right_coef_1 = right_coef_1;
                    min_left_len_1 = left_len_1;
                    min_right_len_1 = right_len_1;
                } else{
                    //printf("break\n");
                    // Roll back 
                    for (int right_delete = right_len_1 ; right_delete >= 1 ; right_delete--){
                        min_right_data_num_1[right_delete] = min_right_data_num_1[right_delete - 1];
                        min_right_exec_time_1[right_delete] = min_right_exec_time_1[right_delete - 1];
                    }
                    min_right_data_num_1[0] = min_left_data_num_1[(left_len_1 - 2)];
                    min_right_exec_time_1[0] = min_left_exec_time_1[(left_len_1 - 2)];
                    right_len_1 += 1;
                    min_left_data_num_1[(left_len_1 - 1)] = 0;
                    min_left_exec_time_1[(left_len_1 - 1)] = 0;
                    left_len_1 -= 1;
                    free(left_coef_1);
                    free(right_coef_1);
                    break;
                } 
            }
        }   
        if ((min_left_error_rate_1 < 5) | (min_right_error_rate_1 < 5)){
            //printf("small enough - break\n");
            // Roll back 
            for (int right_delete = right_len_1 ; right_delete >= 1 ; right_delete--){
                min_right_data_num_1[right_delete] = min_right_data_num_1[right_delete - 1];
                min_right_exec_time_1[right_delete] = min_right_exec_time_1[right_delete - 1];
            }
            min_right_data_num_1[0] = min_left_data_num_1[(left_len_1 - 2)];
            min_right_exec_time_1[0] = min_left_exec_time_1[(left_len_1 - 2)];
            right_len_1 += 1;
            min_left_data_num_1[(left_len_1 - 1)] = 0;
            min_left_exec_time_1[(left_len_1 - 1)] = 0;
            left_len_1 -= 1;
            free(left_coef_1);
            free(right_coef_1);
            break;
        }
        if ((min_left_len_1 < 4) | (min_right_len_1 < 4)){
            //printf("too small data for range - break\n");
            // Roll back 
            for (int right_delete = right_len_1 ; right_delete >= 1 ; right_delete--){
                min_right_data_num_1[right_delete] = min_right_data_num_1[right_delete - 1];
                min_right_exec_time_1[right_delete] = min_right_exec_time_1[right_delete - 1];
            }
            min_right_data_num_1[0] = min_left_data_num_1[(left_len_1 - 2)];
            min_right_exec_time_1[0] = min_left_exec_time_1[(left_len_1 - 2)];
            right_len_1 += 1;
            min_left_data_num_1[(left_len_1 - 1)] = 0;
            min_left_exec_time_1[(left_len_1 - 1)] = 0;
            left_len_1 -= 1;
            free(left_coef_1);
            free(right_coef_1);
            break;
        }
    }
    //printf("phase 1 result: %lf, %lf / boundary: %lf\n", min_left_error_rate_1, min_right_error_rate_1, min_right_data_num_1[0]);
    /*
    for (int x = 0 ; x < EXEC_ORDER + 1 ; x++){
        printf("%e ", min_left_coef_1[x]);
    }
    printf("\n");
    for (int y = 0 ; y < EXEC_ORDER + 1 ; y++){
        printf("%e ", min_right_coef_1[y]);
    }
    printf("\n");
    */
    //print_data(min_left_data_num_1, min_left_len_1);
    //print_data(min_right_data_num_1, min_right_len_1);

    // phase 1 (right moving phase)
    //printf("Phase 2\n");
    double min_left_error_2 = def_left_error;
    double min_right_error_2 = def_right_error;
    double min_left_error_rate_2 = def_left_error_rate;
    double min_right_error_rate_2 = def_right_error_rate;    
    
    double *min_left_coef_2 = (double *)malloc(sizeof(double) * (EXEC_ORDER + 1));
    double *min_right_coef_2 = (double *)malloc(sizeof(double) * (EXEC_ORDER + 1));
    for (int coef_i = 0 ; coef_i < EXEC_ORDER + 1 ; coef_i++){
        min_left_coef_2[coef_i] = def_left_coef[coef_i];
        min_right_coef_2[coef_i] = def_right_coef[coef_i];
    }
    free(def_left_coef);
    free(def_right_coef);
    int min_left_len_2 = def_data1_len;
    int min_right_len_2 = def_data2_len;

    double *min_left_data_num_2 = (double *)malloc(sizeof(double) * total_len);
    double *min_right_data_num_2 = (double *)malloc(sizeof(double) * total_len);
    double *min_left_exec_time_2 = (double *)malloc(sizeof(double) * total_len);
    double *min_right_exec_time_2 = (double *)malloc(sizeof(double) * total_len);

    for (int left_i = 0 ; left_i < def_data1_len ; left_i++){
        min_left_data_num_2[left_i] = data_num1[left_i];
        min_left_exec_time_2[left_i] = exec_time1[left_i];
    }
    for (int right_i = 0 ; right_i < def_data2_len ; right_i++){
        min_right_data_num_2[right_i] = data_num2[right_i];
        min_right_exec_time_2[right_i] = exec_time2[right_i];
    }

    int left_len_2 = def_data1_len;
    int right_len_2 = def_data2_len;

    for (int phase2_rec = 0 ; phase2_rec < def_data1_len ; phase2_rec++){
        for (int right_delete = right_len_2 ; right_delete >= 1 ; right_delete--){
            min_right_data_num_2[right_delete] = min_right_data_num_2[right_delete - 1];
            min_right_exec_time_2[right_delete] = min_right_exec_time_2[right_delete - 1];
        }
        min_right_data_num_2[0] = min_left_data_num_2[(left_len_2 - 2)];
        min_right_exec_time_2[0] = min_left_exec_time_2[(left_len_2 - 2)];
        right_len_2 += 1;
        min_left_data_num_2[(left_len_2 - 1)] = 0;
        min_left_exec_time_2[(left_len_2 - 1)] = 0;
        left_len_2 -= 1;

        //print_data(min_left_data_num_2, left_len_2);
        //print_data(min_right_data_num_2, right_len_2);

        double *left_coef_2 = (double *)malloc(sizeof(double) * (EXEC_ORDER + 1));
        if (get_avg_error(min_left_data_num_2, min_left_exec_time_2, left_len_2, &left_error, &left_error_rate, left_coef_2, first_flag)){
            printf("Error occured in get_avg_error\n");
        }
        double *right_coef_2 = (double *)malloc(sizeof(double) * (EXEC_ORDER + 1));
        if (get_avg_error(min_right_data_num_2, min_right_exec_time_2, right_len_2, &right_error, &right_error_rate, right_coef_2, false)){
            printf("Error occured in get_avg_error\n");
        }     
        //printf("[left] error_rate: %lf [right] error_rate: %lf\n", left_error_rate, right_error_rate);

        if ((left_error_rate < min_left_error_rate_2) & (right_error_rate < min_right_error_rate_2)){
            //printf("case 1\n");
            //printf("updated to %lf, %lf\n", left_error_rate, right_error_rate);
            min_left_error_2 = left_error;
            min_right_error_2 = right_error;
            min_left_error_rate_2 = left_error_rate;
            min_right_error_rate_2 = right_error_rate;
            free(min_left_coef_2);
            free(min_right_coef_2);
            min_left_coef_2 = left_coef_2;
            min_right_coef_2 = right_coef_2;
            min_left_len_2 = left_len_2;
            min_right_len_2 = right_len_2;
        } else if ((left_error_rate > min_left_error_rate_2) & (right_error_rate > min_right_error_rate_2)){
            //printf("case 2\n");
            //printf("break\n");
            // Roll back 
            min_left_data_num_2[left_len_2] = min_right_data_num_2[1];
            min_left_exec_time_2[left_len_2] = min_right_exec_time_2[1];
            left_len_2 += 1;
            for (int right_delete = 0 ; right_delete < (right_len_2 - 1) ; right_delete++){
                min_right_data_num_2[right_delete] = min_right_data_num_2[right_delete + 1];
                min_right_exec_time_2[right_delete] = min_right_exec_time_2[right_delete + 1];
            }
            min_right_data_num_2[(right_len_2 - 1)] = 0;
            min_right_exec_time_2[(right_len_2 - 1)] = 0;
            right_len_2 -= 1;
            free(left_coef_2);
            free(right_coef_2);
            break;
        } else{
            if ((left_error_rate < min_left_error_rate_2) & (right_error_rate > min_right_error_rate_2)){
                //printf("case 3_1\n");
                double left_improved = min_left_error_rate_2 - left_error_rate;
                double right_worsed = right_error_rate - min_right_error_rate_2;
                if (left_improved > right_worsed){
                    //printf("updated to %lf, %lf\n", left_error_rate, right_error_rate);
                    min_left_error_2 = left_error;
                    min_right_error_2 = right_error;
                    min_left_error_rate_2 = left_error_rate;
                    min_right_error_rate_2 = right_error_rate;
                    free(min_left_coef_2);
                    free(min_right_coef_2);
                    min_left_coef_2 = left_coef_2;
                    min_right_coef_2 = right_coef_2;
                    min_left_len_2 = left_len_2;
                    min_right_len_2 = right_len_2;
                } else{
                    //printf("break\n");
                    // Roll back 
                    min_left_data_num_2[left_len_2] = min_right_data_num_2[1];
                    min_left_exec_time_2[left_len_2] = min_right_exec_time_2[1];
                    left_len_2 += 1;
                    for (int right_delete = 0 ; right_delete < (right_len_2 - 1) ; right_delete++){
                        min_right_data_num_2[right_delete] = min_right_data_num_2[right_delete + 1];
                        min_right_exec_time_2[right_delete] = min_right_exec_time_2[right_delete + 1];
                    }
                    min_right_data_num_2[(right_len_2 - 1)] = 0;
                    min_right_exec_time_2[(right_len_2 - 1)] = 0;
                    right_len_2 -= 1;
                    free(left_coef_2);
                    free(right_coef_2);
                    break;
                }
            } else{
                //printf("case 3_2\n");
                double left_worsed = left_error_rate - min_left_error_rate_2;
                double right_improved = min_right_error_rate_2 - right_error_rate;
                if (right_improved > left_worsed){
                    //printf("updated to %lf, %lf\n", left_error_rate, right_error_rate);
                    min_left_error_2 = left_error;
                    min_right_error_2 = right_error;
                    min_left_error_rate_2 = left_error_rate;
                    min_right_error_rate_2 = right_error_rate;
                    free(min_left_coef_2);
                    free(min_right_coef_2);
                    min_left_coef_2 = left_coef_2;
                    min_right_coef_2 = right_coef_2;
                    min_left_len_2 = left_len_2;
                    min_right_len_2 = right_len_2;
                } else{
                    //printf("break\n");
                    // Roll back 
                    min_left_data_num_2[left_len_2] = min_right_data_num_2[1];
                    min_left_exec_time_2[left_len_2] = min_right_exec_time_2[1];
                    left_len_2 += 1;
                    for (int right_delete = 0 ; right_delete < (right_len_2 - 1) ; right_delete++){
                        min_right_data_num_2[right_delete] = min_right_data_num_2[right_delete + 1];
                        min_right_exec_time_2[right_delete] = min_right_exec_time_2[right_delete + 1];
                    }
                    min_right_data_num_2[(right_len_2 - 1)] = 0;
                    min_right_exec_time_2[(right_len_2 - 1)] = 0;
                    right_len_2 -= 1;
                    free(left_coef_2);
                    free(right_coef_2);
                    break;
                } 
            }
        }   
        if ((min_left_error_rate_1 < 5) | (min_right_error_rate_1 < 5)){
            //printf("small enough - break\n");
            // Roll back 
            min_left_data_num_2[left_len_2] = min_right_data_num_2[1];
            min_left_exec_time_2[left_len_2] = min_right_exec_time_2[1];
            left_len_2 += 1;
            for (int right_delete = 0 ; right_delete < (right_len_2 - 1) ; right_delete++){
                min_right_data_num_2[right_delete] = min_right_data_num_2[right_delete + 1];
                min_right_exec_time_2[right_delete] = min_right_exec_time_2[right_delete + 1];
            }
            min_right_data_num_2[(right_len_2 - 1)] = 0;
            min_right_exec_time_2[(right_len_2 - 1)] = 0;
            right_len_2 -= 1;
            free(left_coef_2);
            free(right_coef_2);
            break;
        }
        if ((min_left_len_1 < 4) | (min_right_len_1 < 4)){
            //printf("too small data for range - break\n");
            // Roll back 
            min_left_data_num_2[left_len_2] = min_right_data_num_2[1];
            min_left_exec_time_2[left_len_2] = min_right_exec_time_2[1];
            left_len_2 += 1;
            for (int right_delete = 0 ; right_delete < (right_len_2 - 1) ; right_delete++){
                min_right_data_num_2[right_delete] = min_right_data_num_2[right_delete + 1];
                min_right_exec_time_2[right_delete] = min_right_exec_time_2[right_delete + 1];
            }
            min_right_data_num_2[(right_len_2 - 1)] = 0;
            min_right_exec_time_2[(right_len_2 - 1)] = 0;
            right_len_2 -= 1;
            free(left_coef_2);
            free(right_coef_2);
            break;
        }
    }
    //printf("phase 2 result: %lf, %lf / boundary: %lf\n", min_left_error_rate_2, min_right_error_rate_2, min_right_data_num_2[0]);
    /*
    for (int x = 0 ; x < EXEC_ORDER + 1 ; x++){
        printf("%e ", min_left_coef_2[x]);
    }
    printf("\n");
    for (int y = 0 ; y < EXEC_ORDER + 1 ; y++){
        printf("%e ", min_right_coef_2[y]);
    }
    printf("\n");
    */
    //print_data(min_left_data_num_2, min_left_len_2);
    //print_data(min_right_data_num_2, min_right_len_2);

    //print_data(min_left_data_num_1, min_left_len_1);
    //print_data(min_right_data_num_1, min_right_len_1);

    if (min_left_error_rate_1 + min_right_error_rate_1 < min_left_error_rate_2 + min_right_error_rate_2){
        printf("Final result: %lf, %lf / boundary: %lf\n", min_left_error_rate_1, min_right_error_rate_1, min_right_data_num_1[0]);
        /*for (int x = 0 ; x < EXEC_ORDER + 1 ; x++){
            printf("%e ", min_left_coef_1[x]);
        }
        printf("\n");
        for (int y = 0 ; y < EXEC_ORDER + 1 ; y++){
            printf("%e ", min_right_coef_1[y]);
        }
        printf("\n");*/
        *min_left_data_num = min_left_data_num_1;
        *min_right_data_num = min_right_data_num_1;
        *min_left_exec_time = min_left_exec_time_1;
        *min_right_exec_time = min_right_exec_time_1;
        *min_left_coef = min_left_coef_1;
        *min_right_coef = min_right_coef_1;
        *data1_len = min_left_len_1;
        *data2_len = min_right_len_1;
        free(min_left_data_num_2);
        free(min_right_data_num_2);
        free(min_left_exec_time_2);
        free(min_right_exec_time_2);
        free(min_left_coef_2);
        free(min_right_coef_2);
    } else{
        printf("Final result: %lf, %lf / boundary: %lf\n", min_left_error_rate_2, min_right_error_rate_2, min_right_data_num_2[0]);
        /*for (int x = 0 ; x < EXEC_ORDER + 1 ; x++){
            printf("%e ", min_left_coef_2[x]);
        }
        printf("\n");
        for (int y = 0 ; y < EXEC_ORDER + 1 ; y++){
            printf("%e ", min_right_coef_2[y]);
        }
        printf("\n");*/
        *min_left_data_num = min_left_data_num_2;
        *min_right_data_num = min_right_data_num_2;
        *min_left_exec_time = min_left_exec_time_2;
        *min_right_exec_time = min_right_exec_time_2;
        *min_left_coef = min_left_coef_2;
        *min_right_coef = min_right_coef_2;
        *data1_len = min_left_len_2;
        *data2_len = min_right_len_2;
        free(min_left_data_num_1);
        free(min_right_data_num_1);
        free(min_left_exec_time_1);
        free(min_right_exec_time_1);
        free(min_left_coef_1);
        free(min_right_coef_1);
    }

    return 0;
}

void get_init_values(double*** num1, double*** num2, double*** num3, 
                     double*** exec_time1_out, double*** exec_time2_out, double*** exec_time3_out,
                     int** len1, int** len2, int** len3){
                         
    int data1_len_saved = 15;
    int data2_len_saved = 13;
    int data3_len_saved = 18;

    double data_num1_saved[] = {1.5, 2.5, 6.5, 14, 15, 25, 30, 50, 65, 130, 140, 280, 300, 500, 1300};
    double data_num2_saved[] = {1300, 2800, 3000, 5000, 13000, 15000, 25000, 28000, 33000, 55000, 65000, 75000, 125000};
    double data_num3_saved[] = {125000, 130000, 143000, 150000, 225000, 250000, 308000, 325000, 330000, 375000, 550000, 650000, 700000, 975000, 1400000, 1430000, 2100000, 3080000};
    
    double q1_exec_time1_saved[] = {5.009, 11.191, 7.748, 16.792, 28.235, 30.145, 38.956, 41.345, 35.973, 52.418, 45.241, 72.999, 209.909, 240.505, 365.524};
    double q2_exec_time1_saved[] = {9.35, 11.292, 12.841, 13.251, 20.488, 26.042, 27.193, 35.864, 30.417, 46.946, 33.15, 54.163, 139.75, 193.902, 305.527};
    double q3_exec_time1_saved[] = {7.403, 8.965, 14.224, 15.928, 27.692, 29.636, 0.784, 40.371, 35.787, 56.302, 45.382, 72.221, 220.958, 327.824, 405.367};
    double q4_exec_time1_saved[] = {17.894, 12.516, 12.863, 13.896, 21.687, 25.323, 28.148, 34.996, 32.996, 48.222, 36.216, 52.933, 144.889, 265.951, 330.051};
    double q5_exec_time1_saved[] = {12.797, 11.42, 12.91, 15.846, 28.189, 33.896, 43.234, 46.022, 39.047, 55.375, 46.382, 75.878, 277.066, 326.803, 421.25};
    double q6_exec_time1_saved[] = {10.161, 10.688, 12.009, 13.49, 22.58, 26.02, 33.045, 40.856, 33.935, 52.943, 34.686, 61.955, 174.466, 239.625, 356.558};
    double q7_exec_time1_saved[] = {12.207, 13.605, 14.461, 16.98, 33.153, 33.544, 46.006, 46.649, 36.199, 59.511, 47.827, 81.501, 284.85, 327.834, 456.841};
    double q8_exec_time1_saved[] = {5.164, 12.622, 7.569, 13.963, 21.629, 26.906, 33.316, 40.492, 32.828, 54.775, 36.015, 59.572, 187.089, 271.938, 390.979};
    double q9_exec_time1_saved[] = {81.173, 78.342, 74.583, 76.848, 89.299, 92.651, 110.814, 111.765, 101.522, 124.612, 115.361, 152.165, 439.068, 496.864, 611.651};
    double q10_exec_time1_saved[] = {76.744, 79.285, 92.126, 96.959, 120.581, 124.703, 175.217, 190.55, 133.223, 190.336, 159.885, 219.694, 1118.38, 1119.738, 1217.085};
    double q11_exec_time1_saved[] = {82.316, 91.629, 85.542, 86.28, 107.702, 97.484, 116.438, 121.662, 104.085, 122.37, 110.878, 129.364, 589.264, 494.269, 539.124};

    double q1_exec_time2_saved[] = {365.524, 548.974, 6666.357, 7450.265, 10573.282, 11350.895, 15220.229, 16374.973, 23334.794, 25803.333, 30390.761, 48559.641, 56551.836};
    double q2_exec_time2_saved[] = {305.527, 370.061, 6021.93246334, 6514.26459818, 8481.72458038, 8973.12457391, 11427.35590204, 12162.73070221, 14509.886, 20321.73, 21199.06336971, 30649.077, 46062.151};
    double q3_exec_time2_saved[] = {405.367, 584.49, 7216.43449593, 8025.49679421, 11249.47676199, 12052.41687257, 16048.912387, 17241.97468969, 24134.952, 29738.307, 31736.86129067, 50551.571, 61687.493};
    double q4_exec_time2_saved[] = {330.051, 400.493, 6597.10549806, 7109.06105127, 9155.29350517, 9666.45670223, 12219.92842243, 12985.21420294, 15849.221, 21907.723, 22395.83766147, 31569.845, 48325.145};
    double q5_exec_time2_saved[] = {421.25, 613.809, 9864.14617857, 10846.62041209, 14758.79295158, 15732.42105622, 20574.23208211, 22018.25747001, 32271.319, 35754.92, 39509.61420881, 65646.335, 75013.658};
    double q6_exec_time2_saved[] = {356.558, 418.147, 8935.00350494, 9539.82865238, 11955.61884908, 12558.69199287, 15568.84320857, 16470.20164238, 19916.996, 28217.732, 27523.92327023, 40260.792, 64115.814};
    double q7_exec_time2_saved[] = {456.841, 702.726, 10815.20215599, 11841.04134743, 15927.66562521, 16945.15329738, 22007.72852185, 23518.45646139, 33953.631, 35622.5, 41850.02452749, 69992.293, 79871.8};
    double q8_exec_time2_saved[] = {390.979, 451.671, 8778.50949406, 9439.91505461, 12079.51247548, 12737.91121821, 16020.95718528, 17002.97659032, 20564.634, 30655.974, 29006.43550846, 43267.373, 61718.12};
    double q9_exec_time2_saved[] = {611.651, 901.701, 16873.16079022, 18331.18083296, 24140.19240713, 25586.697604, 32784.93193344, 34933.30485993, 50805.343, 52559.642, 61014.77109314, 106375.62, 119138.578};
    double q10_exec_time2_saved[] = {1217.085, 1486.951, 34104.40485182, 38096.02330834, 53963.1758748, 57905.20692585, 77467.55188106, 83288.39550443, 131299.554, 139747.236, 153285.15724642, 282640.036, 275979.924};
    double q11_exec_time2_saved[] = {539.124, 612.425, 13740.36693347, 15351.51686031, 21755.97804103, 23347.08718315, 31242.88076143, 33592.26880851, 48744.342, 55878.196, 61842.52693009, 113040.877, 116197.875};

    double q1_exec_time3_saved[] = {56551.836, 54036.095, 43052.146, 61071.692, 86508.129, 94670.007, 57944.830, 89096.379, 229580.474, 133318.417, 240975.250, 208061.190, 139562.096, 285402.931, 385307.503, 404717.703, 605279.805, 1205969.281};
    double q2_exec_time3_saved[] = {46062.151, 36930.7716255, 33194.21, 41736.49542082, 59622.25107331, 65539.22415667, 39115.23, 76771.871, 144551.863, 94824.56763492, 195283.74, 157911.44883953, 92798.449, 231350.64857283, 328468.50227745, 346516.425, 501269.13437175, 800323.03};
    double q3_exec_time3_saved[] = {61687.493, 56253.37365761, 45069.838, 63564.71019344, 90068.0256174, 98597.22457359, 62449.838, 90084.871, 230095.489, 139172.33065245, 257091.821, 218708.63103929, 149521.546, 302778.41635731, 413402.38312261, 433311.225, 656418.43931735, 1302605.243};
    double q4_exec_time3_saved[] = {48325.145, 38810.34355586, 38924.262, 43832.96942265, 62562.48563911, 68771.85370615, 41669.582, 76962.051, 149945.698, 99609.51944416, 205844.827, 166716.75043134, 100548.227, 246207.61845195, 353890.32444684, 372984.949, 552478.59096392, 910734.295};
    double q5_exec_time3_saved[] = {75013.658, 68858.42989366, 47366.668, 77549.06833796, 108791.266591, 118752.54243, 62513.73, 95989.188, 315766.676, 165445.4473204, 314395.783, 253034.11470036, 144649.888, 339181.78300541, 445323.72966091, 470954.754, 680506.05433504, 1367070.923};
    double q6_exec_time3_saved[] = {64115.814, 46669.51674702, 42560.047, 52493.20042447, 74065.24772427, 81166.31899731, 41905.492, 82042.596, 187861.985, 116055.71674629, 252727.297, 189820.71700739, 96630.489, 273574.92598765, 381851.58671075, 404462.286, 572297.32875584, 909565.503};
    double q7_exec_time3_saved[] = {79871.8, 72749.59329389, 55270.125, 81935.38078833, 115103.42257276, 125729.18931245, 69447.435, 102812.695, 329552.087, 175890.00215365, 334101.326, 271699.65509181, 157916.653, 367820.24290061, 485594.940487, 513220.959, 730063.62056644, 1389510.781};
    double q8_exec_time3_saved[] = {61718.12, 49625.49544608, 45133.391, 55854.6296957, 78757.65960457, 86238.91552716, 46049.951, 89405.264, 197538.799, 122595.35143136, 260710.662, 197509.8659916, 102993.039, 280352.63686408, 386994.02819621, 409701.388, 585069.44941168, 989253.662};
    double q9_exec_time3_saved[] = {119138.578, 105030.30306953, 70971.661, 118127.9795205, 165469.227651, 180651.13879189, 88398.364, 152488.774, 487207.765, 252413.84648453, 486045.704, 389752.81641627, 213980.835, 527111.23345996, 692429.29846554, 733679.654, 1021928.81897446, 1882207.197};
    double q10_exec_time3_saved[] = {275979.924, 268429.80209396, 149850.802, 301916.39666793, 419697.46880134, 456314.73992464, 145871.085, 283570.55, 1293367.083, 620865.09514693, 1330796.074, 888394.83125547, 351843.433, 1080210.9215306, 1227456.41780535, 1306695.821, 1562435.53665559, 3278640.336};
    double q11_exec_time3_saved[] = {116197.875, 108303.79609046, 53292.176, 121811.98591795, 169302.06215946, 184056.93648885, 57931.305, 115217.056, 539001.221, 250268.27543469, 535615.678, 357110.82368786, 128568.488, 431333.44379791, 482087.57494324, 515894.317, 586774.86681101, 1187134.287};

    int* data1_len = (int *)malloc(sizeof(int) * QUERYNUM);
    int* data2_len = (int *)malloc(sizeof(int) * QUERYNUM);
    int* data3_len = (int *)malloc(sizeof(int) * QUERYNUM);

    double** data_num1 = (double **)malloc(sizeof(double) * QUERYNUM);
    double** data_num2 = (double **)malloc(sizeof(double) * QUERYNUM);
    double** data_num3 = (double **)malloc(sizeof(double) * QUERYNUM);
    double** exec_time1 = (double **)malloc(sizeof(double) * QUERYNUM);
    double** exec_time2 = (double **)malloc(sizeof(double) * QUERYNUM);
    double** exec_time3 = (double **)malloc(sizeof(double) * QUERYNUM);

    for (int i = 0 ; i < QUERYNUM ; i++){
        data_num1[i] = (double *)malloc(sizeof(double) * DATASIZE);
        data_num2[i] = (double *)malloc(sizeof(double) * DATASIZE);
        data_num3[i] = (double *)malloc(sizeof(double) * DATASIZE);
        exec_time1[i] = (double *)malloc(sizeof(double) * DATASIZE);
        exec_time2[i] = (double *)malloc(sizeof(double) * DATASIZE);
        exec_time3[i] = (double *)malloc(sizeof(double) * DATASIZE);
    }

    for (int x = 0 ; x < QUERYNUM ; x++){
        for (int i = 0 ; i < data1_len_saved ; i++){
            data_num1[x][i] = data_num1_saved[i];
            switch (x){
                case 0:  
                    exec_time1[x][i] = q1_exec_time1_saved[i];
                    break;
                case 1:
                    exec_time1[x][i] = q2_exec_time1_saved[i];
                    break;
                case 2:
                    exec_time1[x][i] = q3_exec_time1_saved[i];
                    break;
                case 3:
                    exec_time1[x][i] = q4_exec_time1_saved[i];
                    break;
                case 4:
                    exec_time1[x][i] = q5_exec_time1_saved[i];
                    break;
                case 5:
                    exec_time1[x][i] = q6_exec_time1_saved[i];
                    break;
                case 6:
                    exec_time1[x][i] = q7_exec_time1_saved[i];
                    break;
                case 7:
                    exec_time1[x][i] = q8_exec_time1_saved[i];
                    break;
                case 8:
                    exec_time1[x][i] = q9_exec_time1_saved[i];
                    break;
                case 9:
                    exec_time1[x][i] = q10_exec_time1_saved[i];
                    break;
                case 10:
                    exec_time1[x][i] = q11_exec_time1_saved[i];
                    break;
                default:
                    printf("query number error\n");
            }
        }
        for (int j = 0 ; j < data2_len_saved ; j++){
            data_num2[x][j] = data_num2_saved[j];
            switch (x){
                case 0:  
                    exec_time2[x][j] = q1_exec_time2_saved[j];
                    break;
                case 1:
                    exec_time2[x][j] = q2_exec_time2_saved[j];
                    break;
                case 2:
                    exec_time2[x][j] = q3_exec_time2_saved[j];
                    break;
                case 3:
                    exec_time2[x][j] = q4_exec_time2_saved[j];
                    break;
                case 4:
                    exec_time2[x][j] = q5_exec_time2_saved[j];
                    break;
                case 5:
                    exec_time2[x][j] = q6_exec_time2_saved[j];
                    break;
                case 6:
                    exec_time2[x][j] = q7_exec_time2_saved[j];
                    break;
                case 7:
                    exec_time2[x][j] = q8_exec_time2_saved[j];
                    break;
                case 8:
                    exec_time2[x][j] = q9_exec_time2_saved[j];
                    break;
                case 9:
                    exec_time2[x][j] = q10_exec_time2_saved[j];
                    break;
                case 10:
                    exec_time2[x][j] = q11_exec_time2_saved[j];
                    break;
                default:
                    printf("query number error\n");
            }
        }
        for (int k = 0 ; k < data3_len_saved ; k++){
            data_num3[x][k] = data_num3_saved[k];
            switch (x){
                case 0:  
                    exec_time3[x][k] = q1_exec_time3_saved[k];
                    break;
                case 1:
                    exec_time3[x][k] = q2_exec_time3_saved[k];
                    break;
                case 2:
                    exec_time3[x][k] = q3_exec_time3_saved[k];
                    break;
                case 3:
                    exec_time3[x][k] = q4_exec_time3_saved[k];
                    break;
                case 4:
                    exec_time3[x][k] = q5_exec_time3_saved[k];
                    break;
                case 5:
                    exec_time3[x][k] = q6_exec_time3_saved[k];
                    break;
                case 6:
                    exec_time3[x][k] = q7_exec_time3_saved[k];
                    break;
                case 7:
                    exec_time3[x][k] = q8_exec_time3_saved[k];
                    break;
                case 8:
                    exec_time3[x][k] = q9_exec_time3_saved[k];
                    break;
                case 9:
                    exec_time3[x][k] = q10_exec_time3_saved[k];
                    break;
                case 10:
                    exec_time3[x][k] = q11_exec_time3_saved[k];
                    break;
                default:
                    printf("query number error\n");
            }
        }
    }

    for (int x = 0 ; x < QUERYNUM ; x++){
        data1_len[x] = data1_len_saved;
        data2_len[x] = data2_len_saved;
        data3_len[x] = data3_len_saved;
    }

    *num1 = data_num1;
    *num2 = data_num2;
    *num3 = data_num3;

    *exec_time1_out = exec_time1;
    *exec_time2_out = exec_time2;
    *exec_time3_out = exec_time3;

    *len1 = data1_len;
    *len2 = data2_len;
    *len3 = data3_len;
}

void add_new_data(double** num1, double** num2, double** num3, 
                  double** exec_time1, double** exec_time2, double** exec_time3,
                  int* len1, int* len2, int* len3,
                  double** coef1, double** coef2, double** coef3, 
                  double new_data_num_add, double new_exec_time_add){

    double* data_num1 = *num1;
    double* data_num2 = *num2;
    double* data_num3 = *num3;
    
    double* q1_exec_time1 = *exec_time1;
    double* q1_exec_time2 = *exec_time2;
    double* q1_exec_time3 = *exec_time3;

    int data1_len = *len1;
    int data2_len = *len2;
    int data3_len = *len3;

    double* exec_coef1 = *coef1;
    double* exec_coef2 = *coef2;
    double* exec_coef3 = *coef3;

    if (new_data_num_add <= data_num2[0]){ // data range 1
        for (int i = 0 ; i < data1_len ; i++){
            if (data_num1[i] >= new_data_num_add){
                if (data_num1[i] == new_data_num_add){
                    printf("data already existed -> change to new\n");
                    q1_exec_time1[i] = (q1_exec_time1[i] + new_exec_time_add) / 2;
                    break;
                } else{
                    for (int j = (data1_len - 1) ; j >= i ; j--){
                        data_num1[j + 1] = data_num1[j];
                        q1_exec_time1[j + 1] = q1_exec_time1[j];
                    }
                    data_num1[i] = new_data_num_add;
                    q1_exec_time1[i] = new_exec_time_add;
                    (*len1)++;
                    break;
                }
            }
        }
    }
    else if (new_data_num_add <= data_num3[0]){ // data range 2
        for (int i = 0 ; i < data2_len ; i++){
            if (data_num2[i] >= new_data_num_add){
                if (data_num2[i] == new_data_num_add){
                    printf("data already existed -> change to new\n");
                    q1_exec_time2[i] = (q1_exec_time2[i] + new_exec_time_add) / 2;
                    break;
                } else{
                    for (int j = (data2_len - 1) ; j >= i ; j--){
                        data_num2[j + 1] = data_num2[j];
                        q1_exec_time2[j + 1] = q1_exec_time2[j];
                    }
                    data_num2[i] = new_data_num_add;
                    q1_exec_time2[i] = new_exec_time_add;
                    (*len2)++;
                    break;
                }
            }
        }
    } else{ // data range 3
        for (int i = 0 ; i < data3_len ; i++){
            if (data_num3[i] >= new_data_num_add){
                if (data_num3[i] == new_data_num_add){
                    printf("data already existed -> change to new\n");
                    q1_exec_time3[i] = (q1_exec_time3[i] + new_exec_time_add) / 2;
                    break;
                } else{
                    for (int j = (data3_len - 1) ; j >= i ; j--){
                        data_num3[j + 1] = data_num3[j];
                        q1_exec_time3[j + 1] = q1_exec_time3[j];
                    }
                    data_num3[i] = new_data_num_add;
                    q1_exec_time3[i] = new_exec_time_add;
                    (*len3)++;
                    break;
                }
            }
        }
    }

    if (adjust_range(data_num1, data_num2, q1_exec_time1, q1_exec_time2, &data1_len, &data2_len,
                     &data_num1, &data_num2, &q1_exec_time1, &q1_exec_time2, &exec_coef1, &exec_coef2, true)){
        printf("Error occured in adj 1\n");
    }
    if (adjust_range(data_num2, data_num3, q1_exec_time2, q1_exec_time3, &data2_len, &data3_len,
                     &data_num2, &data_num3, &q1_exec_time2, &q1_exec_time3, &exec_coef2, &exec_coef3, false)){
        printf("Error occured in adj 2\n");
    }
	    
    *coef1 = exec_coef1;
    *coef2 = exec_coef2;
    *coef3 = exec_coef3;
}

/* ----------------------------------------------------------------
 *		routines to obtain user input
 * ----------------------------------------------------------------
 */

/* ----------------
 *	InteractiveBackend() is called for user interactive connections
 *
 *	the string entered by the user is placed in its parameter inBuf,
 *	and we act like a Q message was received.
 *
 *	EOF is returned if end-of-file input is seen; time to shut down.
 * ----------------
 */

static int
InteractiveBackend(StringInfo inBuf)
{
	int			c;				/* character read from getc() */

	/*
	 * display a prompt and obtain input from the user
	 */
	printf("backend> ");
	fflush(stdout);

	resetStringInfo(inBuf);

	/*
	 * Read characters until EOF or the appropriate delimiter is seen.
	 */
	while ((c = interactive_getc()) != EOF)
	{
		if (c == '\n')
		{
			if (UseSemiNewlineNewline)
			{
				/*
				 * In -j mode, semicolon followed by two newlines ends the
				 * command; otherwise treat newline as regular character.
				 */
				if (inBuf->len > 1 &&
					inBuf->data[inBuf->len - 1] == '\n' &&
					inBuf->data[inBuf->len - 2] == ';')
				{
					/* might as well drop the second newline */
					break;
				}
			}
			else
			{
				/*
				 * In plain mode, newline ends the command unless preceded by
				 * backslash.
				 */
				if (inBuf->len > 0 &&
					inBuf->data[inBuf->len - 1] == '\\')
				{
					/* discard backslash from inBuf */
					inBuf->data[--inBuf->len] = '\0';
					/* discard newline too */
					continue;
				}
				else
				{
					/* keep the newline character, but end the command */
					appendStringInfoChar(inBuf, '\n');
					break;
				}
			}
		}

		/* Not newline, or newline treated as regular character */
		appendStringInfoChar(inBuf, (char) c);
	}

	/* No input before EOF signal means time to quit. */
	if (c == EOF && inBuf->len == 0)
		return EOF;

	/*
	 * otherwise we have a user query so process it.
	 */

	/* Add '\0' to make it look the same as message case. */
	appendStringInfoChar(inBuf, (char) '\0');

	/*
	 * if the query echo flag was given, print the query..
	 */
	if (EchoQuery)
		printf("statement: %s\n", inBuf->data);
	fflush(stdout);

	return 'Q';
}

/*
 * interactive_getc -- collect one character from stdin
 *
 * Even though we are not reading from a "client" process, we still want to
 * respond to signals, particularly SIGTERM/SIGQUIT.
 */
static int
interactive_getc(void)
{
	int			c;

	/*
	 * This will not process catchup interrupts or notifications while
	 * reading. But those can't really be relevant for a standalone backend
	 * anyway. To properly handle SIGTERM there's a hack in die() that
	 * directly processes interrupts at this stage...
	 */
	CHECK_FOR_INTERRUPTS();

	c = getc(stdin);

	ProcessClientReadInterrupt(false);

	return c;
}

/* ----------------
 *	SocketBackend()		Is called for frontend-backend connections
 *
 *	Returns the message type code, and loads message body data into inBuf.
 *
 *	EOF is returned if the connection is lost.
 * ----------------
 */
static int
SocketBackend(StringInfo inBuf)
{
	int			qtype;

	/*
	 * Get message type code from the frontend.
	 */
	HOLD_CANCEL_INTERRUPTS();
	pq_startmsgread();
	qtype = pq_getbyte();

	if (qtype == EOF)			/* frontend disconnected */
	{
		if (IsTransactionState())
			ereport(COMMERROR,
					(errcode(ERRCODE_CONNECTION_FAILURE),
					 errmsg("unexpected EOF on client connection with an open transaction")));
		else
		{
			/*
			 * Can't send DEBUG log messages to client at this point. Since
			 * we're disconnecting right away, we don't need to restore
			 * whereToSendOutput.
			 */
			whereToSendOutput = DestNone;
			ereport(DEBUG1,
					(errcode(ERRCODE_CONNECTION_DOES_NOT_EXIST),
					 errmsg("unexpected EOF on client connection")));
		}
		return qtype;
	}

	/*
	 * Validate message type code before trying to read body; if we have lost
	 * sync, better to say "command unknown" than to run out of memory because
	 * we used garbage as a length word.
	 *
	 * This also gives us a place to set the doing_extended_query_message flag
	 * as soon as possible.
	 */
	switch (qtype)
	{
		case 'Q':				/* simple query */
			doing_extended_query_message = false;
			if (PG_PROTOCOL_MAJOR(FrontendProtocol) < 3)
			{
				/* old style without length word; convert */
				if (pq_getstring(inBuf))
				{
					if (IsTransactionState())
						ereport(COMMERROR,
								(errcode(ERRCODE_CONNECTION_FAILURE),
								 errmsg("unexpected EOF on client connection with an open transaction")));
					else
					{
						/*
						 * Can't send DEBUG log messages to client at this
						 * point. Since we're disconnecting right away, we
						 * don't need to restore whereToSendOutput.
						 */
						whereToSendOutput = DestNone;
						ereport(DEBUG1,
								(errcode(ERRCODE_CONNECTION_DOES_NOT_EXIST),
								 errmsg("unexpected EOF on client connection")));
					}
					return EOF;
				}
			}
			break;

		case 'F':				/* fastpath function call */
			doing_extended_query_message = false;
			if (PG_PROTOCOL_MAJOR(FrontendProtocol) < 3)
			{
				if (GetOldFunctionMessage(inBuf))
				{
					if (IsTransactionState())
						ereport(COMMERROR,
								(errcode(ERRCODE_CONNECTION_FAILURE),
								 errmsg("unexpected EOF on client connection with an open transaction")));
					else
					{
						/*
						 * Can't send DEBUG log messages to client at this
						 * point. Since we're disconnecting right away, we
						 * don't need to restore whereToSendOutput.
						 */
						whereToSendOutput = DestNone;
						ereport(DEBUG1,
								(errcode(ERRCODE_CONNECTION_DOES_NOT_EXIST),
								 errmsg("unexpected EOF on client connection")));
					}
					return EOF;
				}
			}
			break;

		case 'X':				/* terminate */
			doing_extended_query_message = false;
			ignore_till_sync = false;
			break;

		case 'B':				/* bind */
		case 'C':				/* close */
		case 'D':				/* describe */
		case 'E':				/* execute */
		case 'H':				/* flush */
		case 'P':				/* parse */
			doing_extended_query_message = true;
			/* these are only legal in protocol 3 */
			if (PG_PROTOCOL_MAJOR(FrontendProtocol) < 3)
				ereport(FATAL,
						(errcode(ERRCODE_PROTOCOL_VIOLATION),
						 errmsg("invalid frontend message type %d", qtype)));
			break;

		case 'S':				/* sync */
			/* stop any active skip-till-Sync */
			ignore_till_sync = false;
			/* mark not-extended, so that a new error doesn't begin skip */
			doing_extended_query_message = false;
			/* only legal in protocol 3 */
			if (PG_PROTOCOL_MAJOR(FrontendProtocol) < 3)
				ereport(FATAL,
						(errcode(ERRCODE_PROTOCOL_VIOLATION),
						 errmsg("invalid frontend message type %d", qtype)));
			break;

		case 'd':				/* copy data */
		case 'c':				/* copy done */
		case 'f':				/* copy fail */
			doing_extended_query_message = false;
			/* these are only legal in protocol 3 */
			if (PG_PROTOCOL_MAJOR(FrontendProtocol) < 3)
				ereport(FATAL,
						(errcode(ERRCODE_PROTOCOL_VIOLATION),
						 errmsg("invalid frontend message type %d", qtype)));
			break;

		default:

			/*
			 * Otherwise we got garbage from the frontend.  We treat this as
			 * fatal because we have probably lost message boundary sync, and
			 * there's no good way to recover.
			 */
			ereport(FATAL,
					(errcode(ERRCODE_PROTOCOL_VIOLATION),
					 errmsg("invalid frontend message type %d", qtype)));
			break;
	}

	/*
	 * In protocol version 3, all frontend messages have a length word next
	 * after the type code; we can read the message contents independently of
	 * the type.
	 */
	if (PG_PROTOCOL_MAJOR(FrontendProtocol) >= 3)
	{
		if (pq_getmessage(inBuf, 0))
			return EOF;			/* suitable message already logged */
	}
	else
		pq_endmsgread();
	RESUME_CANCEL_INTERRUPTS();

	return qtype;
}

/* ----------------
 *		ReadCommand reads a command from either the frontend or
 *		standard input, places it in inBuf, and returns the
 *		message type code (first byte of the message).
 *		EOF is returned if end of file.
 * ----------------
 */
static int
ReadCommand(StringInfo inBuf)
{
	int			result;

	if (whereToSendOutput == DestRemote)
		result = SocketBackend(inBuf);
	else
		result = InteractiveBackend(inBuf);
	return result;
}

/*
 * ProcessClientReadInterrupt() - Process interrupts specific to client reads
 *
 * This is called just before and after low-level reads.
 * 'blocked' is true if no data was available to read and we plan to retry,
 * false if about to read or done reading.
 *
 * Must preserve errno!
 */
void
ProcessClientReadInterrupt(bool blocked)
{
	int			save_errno = errno;

	if (DoingCommandRead)
	{
		/* Check for general interrupts that arrived before/while reading */
		CHECK_FOR_INTERRUPTS();

		/* Process sinval catchup interrupts, if any */
		if (catchupInterruptPending)
			ProcessCatchupInterrupt();

		/* Process notify interrupts, if any */
		if (notifyInterruptPending)
			ProcessNotifyInterrupt();
	}
	else if (ProcDiePending)
	{
		/*
		 * We're dying.  If there is no data available to read, then it's safe
		 * (and sane) to handle that now.  If we haven't tried to read yet,
		 * make sure the process latch is set, so that if there is no data
		 * then we'll come back here and die.  If we're done reading, also
		 * make sure the process latch is set, as we might've undesirably
		 * cleared it while reading.
		 */
		if (blocked)
			CHECK_FOR_INTERRUPTS();
		else
			SetLatch(MyLatch);
	}

	errno = save_errno;
}

/*
 * ProcessClientWriteInterrupt() - Process interrupts specific to client writes
 *
 * This is called just before and after low-level writes.
 * 'blocked' is true if no data could be written and we plan to retry,
 * false if about to write or done writing.
 *
 * Must preserve errno!
 */
void
ProcessClientWriteInterrupt(bool blocked)
{
	int			save_errno = errno;

	if (ProcDiePending)
	{
		/*
		 * We're dying.  If it's not possible to write, then we should handle
		 * that immediately, else a stuck client could indefinitely delay our
		 * response to the signal.  If we haven't tried to write yet, make
		 * sure the process latch is set, so that if the write would block
		 * then we'll come back here and die.  If we're done writing, also
		 * make sure the process latch is set, as we might've undesirably
		 * cleared it while writing.
		 */
		if (blocked)
		{
			/*
			 * Don't mess with whereToSendOutput if ProcessInterrupts wouldn't
			 * do anything.
			 */
			if (InterruptHoldoffCount == 0 && CritSectionCount == 0)
			{
				/*
				 * We don't want to send the client the error message, as a)
				 * that would possibly block again, and b) it would likely
				 * lead to loss of protocol sync because we may have already
				 * sent a partial protocol message.
				 */
				if (whereToSendOutput == DestRemote)
					whereToSendOutput = DestNone;

				CHECK_FOR_INTERRUPTS();
			}
		}
		else
			SetLatch(MyLatch);
	}

	errno = save_errno;
}

/*
 * Do raw parsing (only).
 *
 * A list of parsetrees (RawStmt nodes) is returned, since there might be
 * multiple commands in the given string.
 *
 * NOTE: for interactive queries, it is important to keep this routine
 * separate from the analysis & rewrite stages.  Analysis and rewriting
 * cannot be done in an aborted transaction, since they require access to
 * database tables.  So, we rely on the raw parser to determine whether
 * we've seen a COMMIT or ABORT command; when we are in abort state, other
 * commands are not processed any further than the raw parse stage.
 */
List *
pg_parse_query(const char *query_string)
{
	List	   *raw_parsetree_list;

	TRACE_POSTGRESQL_QUERY_PARSE_START(query_string);

	if (log_parser_stats)
		ResetUsage();

	raw_parsetree_list = raw_parser(query_string);

	if (log_parser_stats)
		ShowUsage("PARSER STATISTICS");

#ifdef COPY_PARSE_PLAN_TREES
	/* Optional debugging check: pass raw parsetrees through copyObject() */
	{
		List	   *new_list = copyObject(raw_parsetree_list);

		/* This checks both copyObject() and the equal() routines... */
		if (!equal(new_list, raw_parsetree_list))
			elog(WARNING, "copyObject() failed to produce an equal raw parse tree");
		else
			raw_parsetree_list = new_list;
	}
#endif

	/*
	 * Currently, outfuncs/readfuncs support is missing for many raw parse
	 * tree nodes, so we don't try to implement WRITE_READ_PARSE_PLAN_TREES
	 * here.
	 */

	TRACE_POSTGRESQL_QUERY_PARSE_DONE(query_string);

	return raw_parsetree_list;
}

/*
 * Given a raw parsetree (gram.y output), and optionally information about
 * types of parameter symbols ($n), perform parse analysis and rule rewriting.
 *
 * A list of Query nodes is returned, since either the analyzer or the
 * rewriter might expand one query to several.
 *
 * NOTE: for reasons mentioned above, this must be separate from raw parsing.
 */
List *
pg_analyze_and_rewrite(RawStmt *parsetree, const char *query_string,
					   Oid *paramTypes, int numParams,
					   QueryEnvironment *queryEnv)
{
	Query	   *query;
	List	   *querytree_list;

	TRACE_POSTGRESQL_QUERY_REWRITE_START(query_string);

	/*
	 * (1) Perform parse analysis.
	 */
	if (log_parser_stats)
		ResetUsage();

	query = parse_analyze(parsetree, query_string, paramTypes, numParams,
						  queryEnv);

	if (log_parser_stats)
		ShowUsage("PARSE ANALYSIS STATISTICS");

	/*
	 * (2) Rewrite the queries, as necessary
	 */
	querytree_list = pg_rewrite_query(query);

	TRACE_POSTGRESQL_QUERY_REWRITE_DONE(query_string);

	return querytree_list;
}

/*
 * Do parse analysis and rewriting.  This is the same as pg_analyze_and_rewrite
 * except that external-parameter resolution is determined by parser callback
 * hooks instead of a fixed list of parameter datatypes.
 */
List *
pg_analyze_and_rewrite_params(RawStmt *parsetree,
							  const char *query_string,
							  ParserSetupHook parserSetup,
							  void *parserSetupArg,
							  QueryEnvironment *queryEnv)
{
	ParseState *pstate;
	Query	   *query;
	List	   *querytree_list;

	Assert(query_string != NULL);	/* required as of 8.4 */

	TRACE_POSTGRESQL_QUERY_REWRITE_START(query_string);

	/*
	 * (1) Perform parse analysis.
	 */
	if (log_parser_stats)
		ResetUsage();

	pstate = make_parsestate(NULL);
	pstate->p_sourcetext = query_string;
	pstate->p_queryEnv = queryEnv;
	(*parserSetup) (pstate, parserSetupArg);

	query = transformTopLevelStmt(pstate, parsetree);

	if (post_parse_analyze_hook)
		(*post_parse_analyze_hook) (pstate, query);

	free_parsestate(pstate);

	if (log_parser_stats)
		ShowUsage("PARSE ANALYSIS STATISTICS");

	/*
	 * (2) Rewrite the queries, as necessary
	 */
	querytree_list = pg_rewrite_query(query);

	TRACE_POSTGRESQL_QUERY_REWRITE_DONE(query_string);

	return querytree_list;
}

/*
 * Perform rewriting of a query produced by parse analysis.
 *
 * Note: query must just have come from the parser, because we do not do
 * AcquireRewriteLocks() on it.
 */
static List *
pg_rewrite_query(Query *query)
{
	List	   *querytree_list;

	if (Debug_print_parse)
		elog_node_display(LOG, "parse tree", query,
						  Debug_pretty_print);

	if (log_parser_stats)
		ResetUsage();

	if (query->commandType == CMD_UTILITY)
	{
		/* don't rewrite utilities, just dump 'em into result list */
		querytree_list = list_make1(query);
	}
	else
	{
		/* rewrite regular queries */
		querytree_list = QueryRewrite(query);
	}

	if (log_parser_stats)
		ShowUsage("REWRITER STATISTICS");

#ifdef COPY_PARSE_PLAN_TREES
	/* Optional debugging check: pass querytree through copyObject() */
	{
		List	   *new_list;

		new_list = copyObject(querytree_list);
		/* This checks both copyObject() and the equal() routines... */
		if (!equal(new_list, querytree_list))
			elog(WARNING, "copyObject() failed to produce equal parse tree");
		else
			querytree_list = new_list;
	}
#endif

#ifdef WRITE_READ_PARSE_PLAN_TREES
	/* Optional debugging check: pass querytree through outfuncs/readfuncs */
	{
		List	   *new_list = NIL;
		ListCell   *lc;

		/*
		 * We currently lack outfuncs/readfuncs support for most utility
		 * statement types, so only attempt to write/read non-utility queries.
		 */
		foreach(lc, querytree_list)
		{
			Query	   *query = castNode(Query, lfirst(lc));

			if (query->commandType != CMD_UTILITY)
			{
				char	   *str = nodeToString(query);
				Query	   *new_query = stringToNodeWithLocations(str);

				/*
				 * queryId is not saved in stored rules, but we must preserve
				 * it here to avoid breaking pg_stat_statements.
				 */
				new_query->queryId = query->queryId;

				new_list = lappend(new_list, new_query);
				pfree(str);
			}
			else
				new_list = lappend(new_list, query);
		}

		/* This checks both outfuncs/readfuncs and the equal() routines... */
		if (!equal(new_list, querytree_list))
			elog(WARNING, "outfuncs/readfuncs failed to produce equal parse tree");
		else
			querytree_list = new_list;
	}
#endif

	if (Debug_print_rewritten)
		elog_node_display(LOG, "rewritten parse tree", querytree_list,
						  Debug_pretty_print);

	return querytree_list;
}


/*
 * Generate a plan for a single already-rewritten query.
 * This is a thin wrapper around planner() and takes the same parameters.
 */
PlannedStmt *
pg_plan_query(Query *querytree, int cursorOptions, ParamListInfo boundParams)
{
	PlannedStmt *plan;

	/* Utility commands have no plans. */
	if (querytree->commandType == CMD_UTILITY)
		return NULL;

	/* Planner must have a snapshot in case it calls user-defined functions. */
	Assert(ActiveSnapshotSet());

	TRACE_POSTGRESQL_QUERY_PLAN_START();

	if (log_planner_stats)
		ResetUsage();

	/* call the optimizer */
	plan = planner(querytree, cursorOptions, boundParams);

	if (log_planner_stats)
		ShowUsage("PLANNER STATISTICS");

#ifdef COPY_PARSE_PLAN_TREES
	/* Optional debugging check: pass plan tree through copyObject() */
	{
		PlannedStmt *new_plan = copyObject(plan);

		/*
		 * equal() currently does not have routines to compare Plan nodes, so
		 * don't try to test equality here.  Perhaps fix someday?
		 */
#ifdef NOT_USED
		/* This checks both copyObject() and the equal() routines... */
		if (!equal(new_plan, plan))
			elog(WARNING, "copyObject() failed to produce an equal plan tree");
		else
#endif
			plan = new_plan;
	}
#endif

#ifdef WRITE_READ_PARSE_PLAN_TREES
	/* Optional debugging check: pass plan tree through outfuncs/readfuncs */
	{
		char	   *str;
		PlannedStmt *new_plan;

		str = nodeToString(plan);
		new_plan = stringToNodeWithLocations(str);
		pfree(str);

		/*
		 * equal() currently does not have routines to compare Plan nodes, so
		 * don't try to test equality here.  Perhaps fix someday?
		 */
#ifdef NOT_USED
		/* This checks both outfuncs/readfuncs and the equal() routines... */
		if (!equal(new_plan, plan))
			elog(WARNING, "outfuncs/readfuncs failed to produce an equal plan tree");
		else
#endif
			plan = new_plan;
	}
#endif

	/*
	 * Print plan if debugging.
	 */
	if (Debug_print_plan)
		elog_node_display(LOG, "plan", plan, Debug_pretty_print);

	TRACE_POSTGRESQL_QUERY_PLAN_DONE();

	return plan;
}

/*
 * Generate plans for a list of already-rewritten queries.
 *
 * For normal optimizable statements, invoke the planner.  For utility
 * statements, just make a wrapper PlannedStmt node.
 *
 * The result is a list of PlannedStmt nodes.
 */
List *
pg_plan_queries(List *querytrees, int cursorOptions, ParamListInfo boundParams)
{
	List	   *stmt_list = NIL;
	ListCell   *query_list;

	foreach(query_list, querytrees)
	{
		Query	   *query = lfirst_node(Query, query_list);
		PlannedStmt *stmt;

		if (query->commandType == CMD_UTILITY)
		{
			/* Utility commands require no planning. */
			stmt = makeNode(PlannedStmt);
			stmt->commandType = CMD_UTILITY;
			stmt->canSetTag = query->canSetTag;
			stmt->utilityStmt = query->utilityStmt;
			stmt->stmt_location = query->stmt_location;
			stmt->stmt_len = query->stmt_len;
		}
		else
		{
			stmt = pg_plan_query(query, cursorOptions, boundParams);
		}

		stmt_list = lappend(stmt_list, stmt);
	}

	return stmt_list;
}


/*
 * exec_simple_query
 *
 * Execute a "simple Query" protocol message.
 */
static void
exec_simple_query(const char *query_string)
{
	printf(" -- exec_simple_query -- \n");
	CommandDest dest = whereToSendOutput;
	MemoryContext oldcontext;
	List	   *parsetree_list;
	ListCell   *parsetree_item;
	bool		save_log_statement_stats = log_statement_stats;
	bool		was_logged = false;
	bool		use_implicit_block;
	char		msec_str[32];

	/*
	 * Report query to various monitoring facilities.
	 */
	debug_query_string = query_string;

	pgstat_report_activity(STATE_RUNNING, query_string);

	TRACE_POSTGRESQL_QUERY_START(query_string);

	/*
	 * We use save_log_statement_stats so ShowUsage doesn't report incorrect
	 * results because ResetUsage wasn't called.
	 */
	if (save_log_statement_stats)
		ResetUsage();

	/*
	 * Start up a transaction command.  All queries generated by the
	 * query_string will be in this same command block, *unless* we find a
	 * BEGIN/COMMIT/ABORT statement; we have to force a new xact command after
	 * one of those, else bad things will happen in xact.c. (Note that this
	 * will normally change current memory context.)
	 */
	start_xact_command();

	/*
	 * Zap any pre-existing unnamed statement.  (While not strictly necessary,
	 * it seems best to define simple-Query mode as if it used the unnamed
	 * statement and portal; this ensures we recover any storage used by prior
	 * unnamed operations.)
	 */
	drop_unnamed_stmt();

	/*
	 * Switch to appropriate context for constructing parsetrees.
	 */
	oldcontext = MemoryContextSwitchTo(MessageContext);

	/*
	 * Do basic parsing of the query or queries (this should be safe even if
	 * we are in aborted transaction state!)
	 */
	//Debug_print_parse = true;
	printf("pg_parse_query (exec_simple_query)\n");	
	parsetree_list = pg_parse_query(query_string);
	
	printf("(parsetree_list debug)\n");
	/*ListCell *pt_item;
	int numcnt = 0;
	foreach(pt_item, parsetree_list){
		printf("-- item %d\n", numcnt++);
		RawStmt *debugparsetree = lfirst_node(RawStmt, pt_item);
		printf("type: %d\n", debugparsetree->type);
		//NodeTag test = T_RawStmt;
		//printf("check num %d\n", test);
		printf("location: %d\n", debugparsetree->stmt_location); 
		printf("len: %d\n", debugparsetree->stmt_len);
	}
	printf("--- \n");*/

	/* Log immediately if dictated by log_statement */
	if (check_log_statement(parsetree_list))
	{
		ereport(LOG,
				(errmsg("statement: %s", query_string),
				 errhidestmt(true),
				 errdetail_execute(parsetree_list)));
		was_logged = true;
	}

	/*
	 * Switch back to transaction context to enter the loop.
	 */
	MemoryContextSwitchTo(oldcontext);

	/*
	 * For historical reasons, if multiple SQL statements are given in a
	 * single "simple Query" message, we execute them as a single transaction,
	 * unless explicit transaction control commands are included to make
	 * portions of the list be separate transactions.  To represent this
	 * behavior properly in the transaction machinery, we use an "implicit"
	 * transaction block.
	 */
	use_implicit_block = (list_length(parsetree_list) > 1);

	/*
	 * Run through the raw parsetree(s) and process each one.
	 */
	foreach(parsetree_item, parsetree_list)
	{
		printf("foreach loop --- ");
		RawStmt    *parsetree = lfirst_node(RawStmt, parsetree_item);
		bool		snapshot_set = false;
		const char *commandTag;
		char		completionTag[COMPLETION_TAG_BUFSIZE];
		List	   *querytree_list,
				   *plantree_list;
		Portal		portal;
		DestReceiver *receiver;
		int16		format;

		/*
		 * Get the command name for use in status display (it also becomes the
		 * default completion tag, down inside PortalRun).  Set ps_status and
		 * do any special start-of-SQL-command processing needed by the
		 * destination.
		 */
		commandTag = CreateCommandTag(parsetree->stmt);

		printf("commandTag: %s\n", commandTag);

		set_ps_display(commandTag, false);

		BeginCommand(commandTag, dest);

		/*
		 * If we are in an aborted transaction, reject all commands except
		 * COMMIT/ABORT.  It is important that this test occur before we try
		 * to do parse analysis, rewrite, or planning, since all those phases
		 * try to do database accesses, which may fail in abort state. (It
		 * might be safe to allow some additional utility commands in this
		 * state, but not many...)
		 */
		if (IsAbortedTransactionBlockState() &&
			!IsTransactionExitStmt(parsetree->stmt))
			ereport(ERROR,
					(errcode(ERRCODE_IN_FAILED_SQL_TRANSACTION),
					 errmsg("current transaction is aborted, "
							"commands ignored until end of transaction block"),
					 errdetail_abort()));

		/* Make sure we are in a transaction command */
		start_xact_command();

		/*
		 * If using an implicit transaction block, and we're not already in a
		 * transaction block, start an implicit block to force this statement
		 * to be grouped together with any following ones.  (We must do this
		 * each time through the loop; otherwise, a COMMIT/ROLLBACK in the
		 * list would cause later statements to not be grouped.)
		 */
		if (use_implicit_block)
			BeginImplicitTransactionBlock();

		/* If we got a cancel signal in parsing or prior command, quit */
		CHECK_FOR_INTERRUPTS();

		/*
		 * Set up a snapshot if parse analysis/planning will need one.
		 */
		if (analyze_requires_snapshot(parsetree))
		{
			PushActiveSnapshot(GetTransactionSnapshot());
			snapshot_set = true;
		}

		/*
		 * OK to analyze, rewrite, and plan this query.
		 *
		 * Switch to appropriate context for constructing querytrees (again,
		 * these must outlive the execution context).
		 */
		oldcontext = MemoryContextSwitchTo(MessageContext);

		querytree_list = pg_analyze_and_rewrite(parsetree, query_string,
												NULL, 0, NULL);

		//ListCell *querytree_cell;
		//numcnt = 0;
		printf("(querytree_list debug)\n");
		/*foreach(querytree_cell, querytree_list){
			Query *tquery = lfirst_node(Query, querytree_cell);
			printf("-- item %d\n", numcnt++);
			printf("type: %d\n", tquery->type);
			printf("location: %d\n", tquery->stmt_location); 
			printf("len: %d\n", tquery->stmt_len);
		}
		printf("--- \n");*/

		// --------------------------------------------------------------------------
		//
		//	Something should be implemented 
		//	(HW checker / HW reconstructor / Predictor / HW compiler)
		//
		// --------------------------------------------------------------------------
		if (HW_ACTIVATED)
			sw_stack_for_hw(query_string, querytree_list);
		
		plantree_list = pg_plan_queries(querytree_list,
										CURSOR_OPT_PARALLEL_OK, NULL);

		//ListCell *plantree_cell;
		//numcnt = 0;
		printf("(plantree_list debug)\n");
		/*foreach(plantree_cell, plantree_list){
			PlannedStmt *ptree = lfirst_node(PlannedStmt, plantree_cell);
			printf("-- item %d\n", numcnt++);
			printf("type: %d\n", ptree->type);
			printf("location: %d\n", ptree->stmt_location); 
			printf("len: %d\n", ptree->stmt_len);
		}
		printf("--- \n");*/

		/* Done with the snapshot used for parsing/planning */
		if (snapshot_set)
			PopActiveSnapshot();

		/* If we got a cancel signal in analysis or planning, quit */
		CHECK_FOR_INTERRUPTS();

		/*
		 * Create unnamed portal to run the query or queries in. If there
		 * already is one, silently drop it.
		 */
		portal = CreatePortal("", true, true);
		/* Don't display the portal in pg_cursors */
		portal->visible = false;

		/*
		 * We don't have to copy anything into the portal, because everything
		 * we are passing here is in MessageContext, which will outlive the
		 * portal anyway.
		 */
		PortalDefineQuery(portal,
						  NULL,
						  query_string,
						  commandTag,
						  plantree_list,
						  NULL);

		/*
		 * Start the portal.  No parameters here.
		 */
		PortalStart(portal, NULL, 0, InvalidSnapshot);

		/*
		 * Select the appropriate output format: text unless we are doing a
		 * FETCH from a binary cursor.  (Pretty grotty to have to do this here
		 * --- but it avoids grottiness in other places.  Ah, the joys of
		 * backward compatibility...)
		 */
		format = 0;				/* TEXT is default */
		if (IsA(parsetree->stmt, FetchStmt))
		{
			FetchStmt  *stmt = (FetchStmt *) parsetree->stmt;

			if (!stmt->ismove)
			{
				Portal		fportal = GetPortalByName(stmt->portalname);

				if (PortalIsValid(fportal) &&
					(fportal->cursorOptions & CURSOR_OPT_BINARY))
					format = 1; /* BINARY */
			}
		}
		PortalSetResultFormat(portal, 1, &format);

		/*
		 * Now we can create the destination receiver object.
		 */
		receiver = CreateDestReceiver(dest);
		if (dest == DestRemote)
			SetRemoteDestReceiverParams(receiver, portal);

		/*
		 * Switch back to transaction context for execution.
		 */
		MemoryContextSwitchTo(oldcontext);

		/*
		 * Run the portal to completion, and then drop it (and the receiver).
		 */
		(void) PortalRun(portal,
						 FETCH_ALL,
						 true,	/* always top level */
						 true,
						 receiver,
						 receiver,
						 completionTag);

		receiver->rDestroy(receiver);

		PortalDrop(portal, false);

		if (lnext(parsetree_item) == NULL)
		{
			/*
			 * If this is the last parsetree of the query string, close down
			 * transaction statement before reporting command-complete.  This
			 * is so that any end-of-transaction errors are reported before
			 * the command-complete message is issued, to avoid confusing
			 * clients who will expect either a command-complete message or an
			 * error, not one and then the other.  Also, if we're using an
			 * implicit transaction block, we must close that out first.
			 */
			if (use_implicit_block)
				EndImplicitTransactionBlock();
			finish_xact_command();
		}
		else if (IsA(parsetree->stmt, TransactionStmt))
		{
			/*
			 * If this was a transaction control statement, commit it. We will
			 * start a new xact command for the next command.
			 */
			finish_xact_command();
		}
		else
		{
			/*
			 * We need a CommandCounterIncrement after every query, except
			 * those that start or end a transaction block.
			 */
			CommandCounterIncrement();
		}

		/*
		 * Tell client that we're done with this query.  Note we emit exactly
		 * one EndCommand report for each raw parsetree, thus one for each SQL
		 * command the client sent, regardless of rewriting. (But a command
		 * aborted by error will not send an EndCommand report at all.)
		 */
		EndCommand(completionTag, dest);
	}							/* end loop over parsetrees */

	/*
	 * Close down transaction statement, if one is open.  (This will only do
	 * something if the parsetree list was empty; otherwise the last loop
	 * iteration already did it.)
	 */
	finish_xact_command();

	/*
	 * If there were no parsetrees, return EmptyQueryResponse message.
	 */
	if (!parsetree_list)
		NullCommand(dest);

	/*
	 * Emit duration logging if appropriate.
	 */
	switch (check_log_duration(msec_str, was_logged))
	{
		case 1:
			ereport(LOG,
					(errmsg("duration: %s ms", msec_str),
					 errhidestmt(true)));
			break;
		case 2:
			ereport(LOG,
					(errmsg("duration: %s ms  statement: %s",
							msec_str, query_string),
					 errhidestmt(true),
					 errdetail_execute(parsetree_list)));
			break;
	}

	if (save_log_statement_stats)
		ShowUsage("QUERY STATISTICS");

	TRACE_POSTGRESQL_QUERY_DONE(query_string);

	debug_query_string = NULL;
}

/*
 * exec_parse_message
 *
 * Execute a "Parse" protocol message.
 */
static void
exec_parse_message(const char *query_string,	/* string to execute */
				   const char *stmt_name,	/* name for prepared stmt */
				   Oid *paramTypes, /* parameter types */
				   int numParams)	/* number of parameters */
{
	MemoryContext unnamed_stmt_context = NULL;
	MemoryContext oldcontext;
	List	   *parsetree_list;
	RawStmt    *raw_parse_tree;
	const char *commandTag;
	List	   *querytree_list;
	CachedPlanSource *psrc;
	bool		is_named;
	bool		save_log_statement_stats = log_statement_stats;
	char		msec_str[32];

	/*
	 * Report query to various monitoring facilities.
	 */
	debug_query_string = query_string;

	pgstat_report_activity(STATE_RUNNING, query_string);

	set_ps_display("PARSE", false);

	if (save_log_statement_stats)
		ResetUsage();

	ereport(DEBUG2,
			(errmsg("parse %s: %s",
					*stmt_name ? stmt_name : "<unnamed>",
					query_string)));

	/*
	 * Start up a transaction command so we can run parse analysis etc. (Note
	 * that this will normally change current memory context.) Nothing happens
	 * if we are already in one.  This also arms the statement timeout if
	 * necessary.
	 */
	start_xact_command();

	/*
	 * Switch to appropriate context for constructing parsetrees.
	 *
	 * We have two strategies depending on whether the prepared statement is
	 * named or not.  For a named prepared statement, we do parsing in
	 * MessageContext and copy the finished trees into the prepared
	 * statement's plancache entry; then the reset of MessageContext releases
	 * temporary space used by parsing and rewriting. For an unnamed prepared
	 * statement, we assume the statement isn't going to hang around long, so
	 * getting rid of temp space quickly is probably not worth the costs of
	 * copying parse trees.  So in this case, we create the plancache entry's
	 * query_context here, and do all the parsing work therein.
	 */
	is_named = (stmt_name[0] != '\0');
	if (is_named)
	{
		/* Named prepared statement --- parse in MessageContext */
		oldcontext = MemoryContextSwitchTo(MessageContext);
	}
	else
	{
		/* Unnamed prepared statement --- release any prior unnamed stmt */
		drop_unnamed_stmt();
		/* Create context for parsing */
		unnamed_stmt_context =
			AllocSetContextCreate(MessageContext,
								  "unnamed prepared statement",
								  ALLOCSET_DEFAULT_SIZES);
		oldcontext = MemoryContextSwitchTo(unnamed_stmt_context);
	}

	/*
	 * Do basic parsing of the query or queries (this should be safe even if
	 * we are in aborted transaction state!)
	 */
	parsetree_list = pg_parse_query(query_string);

	/*
	 * We only allow a single user statement in a prepared statement. This is
	 * mainly to keep the protocol simple --- otherwise we'd need to worry
	 * about multiple result tupdescs and things like that.
	 */
	if (list_length(parsetree_list) > 1)
		ereport(ERROR,
				(errcode(ERRCODE_SYNTAX_ERROR),
				 errmsg("cannot insert multiple commands into a prepared statement")));

	if (parsetree_list != NIL)
	{
		Query	   *query;
		bool		snapshot_set = false;

		raw_parse_tree = linitial_node(RawStmt, parsetree_list);

		/*
		 * Get the command name for possible use in status display.
		 */
		commandTag = CreateCommandTag(raw_parse_tree->stmt);

		/*
		 * If we are in an aborted transaction, reject all commands except
		 * COMMIT/ROLLBACK.  It is important that this test occur before we
		 * try to do parse analysis, rewrite, or planning, since all those
		 * phases try to do database accesses, which may fail in abort state.
		 * (It might be safe to allow some additional utility commands in this
		 * state, but not many...)
		 */
		if (IsAbortedTransactionBlockState() &&
			!IsTransactionExitStmt(raw_parse_tree->stmt))
			ereport(ERROR,
					(errcode(ERRCODE_IN_FAILED_SQL_TRANSACTION),
					 errmsg("current transaction is aborted, "
							"commands ignored until end of transaction block"),
					 errdetail_abort()));

		/*
		 * Create the CachedPlanSource before we do parse analysis, since it
		 * needs to see the unmodified raw parse tree.
		 */
		psrc = CreateCachedPlan(raw_parse_tree, query_string, commandTag);

		/*
		 * Set up a snapshot if parse analysis will need one.
		 */
		if (analyze_requires_snapshot(raw_parse_tree))
		{
			PushActiveSnapshot(GetTransactionSnapshot());
			snapshot_set = true;
		}

		/*
		 * Analyze and rewrite the query.  Note that the originally specified
		 * parameter set is not required to be complete, so we have to use
		 * parse_analyze_varparams().
		 */
		if (log_parser_stats)
			ResetUsage();

		query = parse_analyze_varparams(raw_parse_tree,
										query_string,
										&paramTypes,
										&numParams);

		/*
		 * Check all parameter types got determined.
		 */
		for (int i = 0; i < numParams; i++)
		{
			Oid			ptype = paramTypes[i];

			if (ptype == InvalidOid || ptype == UNKNOWNOID)
				ereport(ERROR,
						(errcode(ERRCODE_INDETERMINATE_DATATYPE),
						 errmsg("could not determine data type of parameter $%d",
								i + 1)));
		}

		if (log_parser_stats)
			ShowUsage("PARSE ANALYSIS STATISTICS");

		querytree_list = pg_rewrite_query(query);

		/* Done with the snapshot used for parsing */
		if (snapshot_set)
			PopActiveSnapshot();
	}
	else
	{
		/* Empty input string.  This is legal. */
		raw_parse_tree = NULL;
		commandTag = NULL;
		psrc = CreateCachedPlan(raw_parse_tree, query_string, commandTag);
		querytree_list = NIL;
	}

	/*
	 * CachedPlanSource must be a direct child of MessageContext before we
	 * reparent unnamed_stmt_context under it, else we have a disconnected
	 * circular subgraph.  Klugy, but less so than flipping contexts even more
	 * above.
	 */
	if (unnamed_stmt_context)
		MemoryContextSetParent(psrc->context, MessageContext);

	/* Finish filling in the CachedPlanSource */
	CompleteCachedPlan(psrc,
					   querytree_list,
					   unnamed_stmt_context,
					   paramTypes,
					   numParams,
					   NULL,
					   NULL,
					   CURSOR_OPT_PARALLEL_OK,	/* allow parallel mode */
					   true);	/* fixed result */

	/* If we got a cancel signal during analysis, quit */
	CHECK_FOR_INTERRUPTS();

	if (is_named)
	{
		/*
		 * Store the query as a prepared statement.
		 */
		StorePreparedStatement(stmt_name, psrc, false);
	}
	else
	{
		/*
		 * We just save the CachedPlanSource into unnamed_stmt_psrc.
		 */
		SaveCachedPlan(psrc);
		unnamed_stmt_psrc = psrc;
	}

	MemoryContextSwitchTo(oldcontext);

	/*
	 * We do NOT close the open transaction command here; that only happens
	 * when the client sends Sync.  Instead, do CommandCounterIncrement just
	 * in case something happened during parse/plan.
	 */
	CommandCounterIncrement();

	/*
	 * Send ParseComplete.
	 */
	if (whereToSendOutput == DestRemote)
		pq_putemptymessage('1');

	/*
	 * Emit duration logging if appropriate.
	 */
	switch (check_log_duration(msec_str, false))
	{
		case 1:
			ereport(LOG,
					(errmsg("duration: %s ms", msec_str),
					 errhidestmt(true)));
			break;
		case 2:
			ereport(LOG,
					(errmsg("duration: %s ms  parse %s: %s",
							msec_str,
							*stmt_name ? stmt_name : "<unnamed>",
							query_string),
					 errhidestmt(true)));
			break;
	}

	if (save_log_statement_stats)
		ShowUsage("PARSE MESSAGE STATISTICS");

	debug_query_string = NULL;
}

/*
 * exec_bind_message
 *
 * Process a "Bind" message to create a portal from a prepared statement
 */
static void
exec_bind_message(StringInfo input_message)
{
	const char *portal_name;
	const char *stmt_name;
	int			numPFormats;
	int16	   *pformats = NULL;
	int			numParams;
	int			numRFormats;
	int16	   *rformats = NULL;
	CachedPlanSource *psrc;
	CachedPlan *cplan;
	Portal		portal;
	char	   *query_string;
	char	   *saved_stmt_name;
	ParamListInfo params;
	MemoryContext oldContext;
	bool		save_log_statement_stats = log_statement_stats;
	bool		snapshot_set = false;
	char		msec_str[32];

	/* Get the fixed part of the message */
	portal_name = pq_getmsgstring(input_message);
	stmt_name = pq_getmsgstring(input_message);

	ereport(DEBUG2,
			(errmsg("bind %s to %s",
					*portal_name ? portal_name : "<unnamed>",
					*stmt_name ? stmt_name : "<unnamed>")));

	/* Find prepared statement */
	if (stmt_name[0] != '\0')
	{
		PreparedStatement *pstmt;

		pstmt = FetchPreparedStatement(stmt_name, true);
		psrc = pstmt->plansource;
	}
	else
	{
		/* special-case the unnamed statement */
		psrc = unnamed_stmt_psrc;
		if (!psrc)
			ereport(ERROR,
					(errcode(ERRCODE_UNDEFINED_PSTATEMENT),
					 errmsg("unnamed prepared statement does not exist")));
	}

	/*
	 * Report query to various monitoring facilities.
	 */
	debug_query_string = psrc->query_string;

	pgstat_report_activity(STATE_RUNNING, psrc->query_string);

	set_ps_display("BIND", false);

	if (save_log_statement_stats)
		ResetUsage();

	/*
	 * Start up a transaction command so we can call functions etc. (Note that
	 * this will normally change current memory context.) Nothing happens if
	 * we are already in one.  This also arms the statement timeout if
	 * necessary.
	 */
	start_xact_command();

	/* Switch back to message context */
	MemoryContextSwitchTo(MessageContext);

	/* Get the parameter format codes */
	numPFormats = pq_getmsgint(input_message, 2);
	if (numPFormats > 0)
	{
		pformats = (int16 *) palloc(numPFormats * sizeof(int16));
		for (int i = 0; i < numPFormats; i++)
			pformats[i] = pq_getmsgint(input_message, 2);
	}

	/* Get the parameter value count */
	numParams = pq_getmsgint(input_message, 2);

	if (numPFormats > 1 && numPFormats != numParams)
		ereport(ERROR,
				(errcode(ERRCODE_PROTOCOL_VIOLATION),
				 errmsg("bind message has %d parameter formats but %d parameters",
						numPFormats, numParams)));

	if (numParams != psrc->num_params)
		ereport(ERROR,
				(errcode(ERRCODE_PROTOCOL_VIOLATION),
				 errmsg("bind message supplies %d parameters, but prepared statement \"%s\" requires %d",
						numParams, stmt_name, psrc->num_params)));

	/*
	 * If we are in aborted transaction state, the only portals we can
	 * actually run are those containing COMMIT or ROLLBACK commands. We
	 * disallow binding anything else to avoid problems with infrastructure
	 * that expects to run inside a valid transaction.  We also disallow
	 * binding any parameters, since we can't risk calling user-defined I/O
	 * functions.
	 */
	if (IsAbortedTransactionBlockState() &&
		(!(psrc->raw_parse_tree &&
		   IsTransactionExitStmt(psrc->raw_parse_tree->stmt)) ||
		 numParams != 0))
		ereport(ERROR,
				(errcode(ERRCODE_IN_FAILED_SQL_TRANSACTION),
				 errmsg("current transaction is aborted, "
						"commands ignored until end of transaction block"),
				 errdetail_abort()));

	/*
	 * Create the portal.  Allow silent replacement of an existing portal only
	 * if the unnamed portal is specified.
	 */
	if (portal_name[0] == '\0')
		portal = CreatePortal(portal_name, true, true);
	else
		portal = CreatePortal(portal_name, false, false);

	/*
	 * Prepare to copy stuff into the portal's memory context.  We do all this
	 * copying first, because it could possibly fail (out-of-memory) and we
	 * don't want a failure to occur between GetCachedPlan and
	 * PortalDefineQuery; that would result in leaking our plancache refcount.
	 */
	oldContext = MemoryContextSwitchTo(portal->portalContext);

	/* Copy the plan's query string into the portal */
	query_string = pstrdup(psrc->query_string);

	/* Likewise make a copy of the statement name, unless it's unnamed */
	if (stmt_name[0])
		saved_stmt_name = pstrdup(stmt_name);
	else
		saved_stmt_name = NULL;

	/*
	 * Set a snapshot if we have parameters to fetch (since the input
	 * functions might need it) or the query isn't a utility command (and
	 * hence could require redoing parse analysis and planning).  We keep the
	 * snapshot active till we're done, so that plancache.c doesn't have to
	 * take new ones.
	 */
	if (numParams > 0 ||
		(psrc->raw_parse_tree &&
		 analyze_requires_snapshot(psrc->raw_parse_tree)))
	{
		PushActiveSnapshot(GetTransactionSnapshot());
		snapshot_set = true;
	}

	/*
	 * Fetch parameters, if any, and store in the portal's memory context.
	 */
	if (numParams > 0)
	{
		params = makeParamList(numParams);

		for (int paramno = 0; paramno < numParams; paramno++)
		{
			Oid			ptype = psrc->param_types[paramno];
			int32		plength;
			Datum		pval;
			bool		isNull;
			StringInfoData pbuf;
			char		csave;
			int16		pformat;

			plength = pq_getmsgint(input_message, 4);
			isNull = (plength == -1);

			if (!isNull)
			{
				const char *pvalue = pq_getmsgbytes(input_message, plength);

				/*
				 * Rather than copying data around, we just set up a phony
				 * StringInfo pointing to the correct portion of the message
				 * buffer.  We assume we can scribble on the message buffer so
				 * as to maintain the convention that StringInfos have a
				 * trailing null.  This is grotty but is a big win when
				 * dealing with very large parameter strings.
				 */
				pbuf.data = unconstify(char *, pvalue);
				pbuf.maxlen = plength + 1;
				pbuf.len = plength;
				pbuf.cursor = 0;

				csave = pbuf.data[plength];
				pbuf.data[plength] = '\0';
			}
			else
			{
				pbuf.data = NULL;	/* keep compiler quiet */
				csave = 0;
			}

			if (numPFormats > 1)
				pformat = pformats[paramno];
			else if (numPFormats > 0)
				pformat = pformats[0];
			else
				pformat = 0;	/* default = text */

			if (pformat == 0)	/* text mode */
			{
				Oid			typinput;
				Oid			typioparam;
				char	   *pstring;

				getTypeInputInfo(ptype, &typinput, &typioparam);

				/*
				 * We have to do encoding conversion before calling the
				 * typinput routine.
				 */
				if (isNull)
					pstring = NULL;
				else
					pstring = pg_client_to_server(pbuf.data, plength);

				pval = OidInputFunctionCall(typinput, pstring, typioparam, -1);

				/* Free result of encoding conversion, if any */
				if (pstring && pstring != pbuf.data)
					pfree(pstring);
			}
			else if (pformat == 1)	/* binary mode */
			{
				Oid			typreceive;
				Oid			typioparam;
				StringInfo	bufptr;

				/*
				 * Call the parameter type's binary input converter
				 */
				getTypeBinaryInputInfo(ptype, &typreceive, &typioparam);

				if (isNull)
					bufptr = NULL;
				else
					bufptr = &pbuf;

				pval = OidReceiveFunctionCall(typreceive, bufptr, typioparam, -1);

				/* Trouble if it didn't eat the whole buffer */
				if (!isNull && pbuf.cursor != pbuf.len)
					ereport(ERROR,
							(errcode(ERRCODE_INVALID_BINARY_REPRESENTATION),
							 errmsg("incorrect binary data format in bind parameter %d",
									paramno + 1)));
			}
			else
			{
				ereport(ERROR,
						(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
						 errmsg("unsupported format code: %d",
								pformat)));
				pval = 0;		/* keep compiler quiet */
			}

			/* Restore message buffer contents */
			if (!isNull)
				pbuf.data[plength] = csave;

			params->params[paramno].value = pval;
			params->params[paramno].isnull = isNull;

			/*
			 * We mark the params as CONST.  This ensures that any custom plan
			 * makes full use of the parameter values.
			 */
			params->params[paramno].pflags = PARAM_FLAG_CONST;
			params->params[paramno].ptype = ptype;
		}
	}
	else
		params = NULL;

	/* Done storing stuff in portal's context */
	MemoryContextSwitchTo(oldContext);

	/* Get the result format codes */
	numRFormats = pq_getmsgint(input_message, 2);
	if (numRFormats > 0)
	{
		rformats = (int16 *) palloc(numRFormats * sizeof(int16));
		for (int i = 0; i < numRFormats; i++)
			rformats[i] = pq_getmsgint(input_message, 2);
	}

	pq_getmsgend(input_message);

	/*
	 * Obtain a plan from the CachedPlanSource.  Any cruft from (re)planning
	 * will be generated in MessageContext.  The plan refcount will be
	 * assigned to the Portal, so it will be released at portal destruction.
	 */
	cplan = GetCachedPlan(psrc, params, false, NULL);

	/*
	 * Now we can define the portal.
	 *
	 * DO NOT put any code that could possibly throw an error between the
	 * above GetCachedPlan call and here.
	 */
	PortalDefineQuery(portal,
					  saved_stmt_name,
					  query_string,
					  psrc->commandTag,
					  cplan->stmt_list,
					  cplan);

	/* Done with the snapshot used for parameter I/O and parsing/planning */
	if (snapshot_set)
		PopActiveSnapshot();

	/*
	 * And we're ready to start portal execution.
	 */
	PortalStart(portal, params, 0, InvalidSnapshot);

	/*
	 * Apply the result format requests to the portal.
	 */
	PortalSetResultFormat(portal, numRFormats, rformats);

	/*
	 * Send BindComplete.
	 */
	if (whereToSendOutput == DestRemote)
		pq_putemptymessage('2');

	/*
	 * Emit duration logging if appropriate.
	 */
	switch (check_log_duration(msec_str, false))
	{
		case 1:
			ereport(LOG,
					(errmsg("duration: %s ms", msec_str),
					 errhidestmt(true)));
			break;
		case 2:
			ereport(LOG,
					(errmsg("duration: %s ms  bind %s%s%s: %s",
							msec_str,
							*stmt_name ? stmt_name : "<unnamed>",
							*portal_name ? "/" : "",
							*portal_name ? portal_name : "",
							psrc->query_string),
					 errhidestmt(true),
					 errdetail_params(params)));
			break;
	}

	if (save_log_statement_stats)
		ShowUsage("BIND MESSAGE STATISTICS");

	debug_query_string = NULL;
}

/*
 * exec_execute_message
 *
 * Process an "Execute" message for a portal
 */
static void
exec_execute_message(const char *portal_name, long max_rows)
{
	CommandDest dest;
	DestReceiver *receiver;
	Portal		portal;
	bool		completed;
	char		completionTag[COMPLETION_TAG_BUFSIZE];
	const char *sourceText;
	const char *prepStmtName;
	ParamListInfo portalParams;
	bool		save_log_statement_stats = log_statement_stats;
	bool		is_xact_command;
	bool		execute_is_fetch;
	bool		was_logged = false;
	char		msec_str[32];

	/* Adjust destination to tell printtup.c what to do */
	dest = whereToSendOutput;
	if (dest == DestRemote)
		dest = DestRemoteExecute;

	portal = GetPortalByName(portal_name);
	if (!PortalIsValid(portal))
		ereport(ERROR,
				(errcode(ERRCODE_UNDEFINED_CURSOR),
				 errmsg("portal \"%s\" does not exist", portal_name)));

	/*
	 * If the original query was a null string, just return
	 * EmptyQueryResponse.
	 */
	if (portal->commandTag == NULL)
	{
		Assert(portal->stmts == NIL);
		NullCommand(dest);
		return;
	}

	/* Does the portal contain a transaction command? */
	is_xact_command = IsTransactionStmtList(portal->stmts);

	/*
	 * We must copy the sourceText and prepStmtName into MessageContext in
	 * case the portal is destroyed during finish_xact_command. Can avoid the
	 * copy if it's not an xact command, though.
	 */
	if (is_xact_command)
	{
		sourceText = pstrdup(portal->sourceText);
		if (portal->prepStmtName)
			prepStmtName = pstrdup(portal->prepStmtName);
		else
			prepStmtName = "<unnamed>";

		/*
		 * An xact command shouldn't have any parameters, which is a good
		 * thing because they wouldn't be around after finish_xact_command.
		 */
		portalParams = NULL;
	}
	else
	{
		sourceText = portal->sourceText;
		if (portal->prepStmtName)
			prepStmtName = portal->prepStmtName;
		else
			prepStmtName = "<unnamed>";
		portalParams = portal->portalParams;
	}

	/*
	 * Report query to various monitoring facilities.
	 */
	debug_query_string = sourceText;

	pgstat_report_activity(STATE_RUNNING, sourceText);

	set_ps_display(portal->commandTag, false);

	if (save_log_statement_stats)
		ResetUsage();

	BeginCommand(portal->commandTag, dest);

	/*
	 * Create dest receiver in MessageContext (we don't want it in transaction
	 * context, because that may get deleted if portal contains VACUUM).
	 */
	receiver = CreateDestReceiver(dest);
	if (dest == DestRemoteExecute)
		SetRemoteDestReceiverParams(receiver, portal);

	/*
	 * Ensure we are in a transaction command (this should normally be the
	 * case already due to prior BIND).
	 */
	start_xact_command();

	/*
	 * If we re-issue an Execute protocol request against an existing portal,
	 * then we are only fetching more rows rather than completely re-executing
	 * the query from the start. atStart is never reset for a v3 portal, so we
	 * are safe to use this check.
	 */
	execute_is_fetch = !portal->atStart;

	/* Log immediately if dictated by log_statement */
	if (check_log_statement(portal->stmts))
	{
		ereport(LOG,
				(errmsg("%s %s%s%s: %s",
						execute_is_fetch ?
						_("execute fetch from") :
						_("execute"),
						prepStmtName,
						*portal_name ? "/" : "",
						*portal_name ? portal_name : "",
						sourceText),
				 errhidestmt(true),
				 errdetail_params(portalParams)));
		was_logged = true;
	}

	/*
	 * If we are in aborted transaction state, the only portals we can
	 * actually run are those containing COMMIT or ROLLBACK commands.
	 */
	if (IsAbortedTransactionBlockState() &&
		!IsTransactionExitStmtList(portal->stmts))
		ereport(ERROR,
				(errcode(ERRCODE_IN_FAILED_SQL_TRANSACTION),
				 errmsg("current transaction is aborted, "
						"commands ignored until end of transaction block"),
				 errdetail_abort()));

	/* Check for cancel signal before we start execution */
	CHECK_FOR_INTERRUPTS();

	/*
	 * Okay to run the portal.
	 */
	if (max_rows <= 0)
		max_rows = FETCH_ALL;

	completed = PortalRun(portal,
						  max_rows,
						  true, /* always top level */
						  !execute_is_fetch && max_rows == FETCH_ALL,
						  receiver,
						  receiver,
						  completionTag);

	receiver->rDestroy(receiver);

	if (completed)
	{
		if (is_xact_command)
		{
			/*
			 * If this was a transaction control statement, commit it.  We
			 * will start a new xact command for the next command (if any).
			 */
			finish_xact_command();
		}
		else
		{
			/*
			 * We need a CommandCounterIncrement after every query, except
			 * those that start or end a transaction block.
			 */
			CommandCounterIncrement();

			/* full command has been executed, reset timeout */
			disable_statement_timeout();
		}

		/* Send appropriate CommandComplete to client */
		EndCommand(completionTag, dest);
	}
	else
	{
		/* Portal run not complete, so send PortalSuspended */
		if (whereToSendOutput == DestRemote)
			pq_putemptymessage('s');
	}

	/*
	 * Emit duration logging if appropriate.
	 */
	switch (check_log_duration(msec_str, was_logged))
	{
		case 1:
			ereport(LOG,
					(errmsg("duration: %s ms", msec_str),
					 errhidestmt(true)));
			break;
		case 2:
			ereport(LOG,
					(errmsg("duration: %s ms  %s %s%s%s: %s",
							msec_str,
							execute_is_fetch ?
							_("execute fetch from") :
							_("execute"),
							prepStmtName,
							*portal_name ? "/" : "",
							*portal_name ? portal_name : "",
							sourceText),
					 errhidestmt(true),
					 errdetail_params(portalParams)));
			break;
	}

	if (save_log_statement_stats)
		ShowUsage("EXECUTE MESSAGE STATISTICS");

	debug_query_string = NULL;
}

/*
 * check_log_statement
 *		Determine whether command should be logged because of log_statement
 *
 * stmt_list can be either raw grammar output or a list of planned
 * statements
 */
static bool
check_log_statement(List *stmt_list)
{
	ListCell   *stmt_item;

	if (log_statement == LOGSTMT_NONE)
		return false;
	if (log_statement == LOGSTMT_ALL)
		return true;

	/* Else we have to inspect the statement(s) to see whether to log */
	foreach(stmt_item, stmt_list)
	{
		Node	   *stmt = (Node *) lfirst(stmt_item);

		if (GetCommandLogLevel(stmt) <= log_statement)
			return true;
	}

	return false;
}

/*
 * check_log_duration
 *		Determine whether current command's duration should be logged
 *		We also check if this statement in this transaction must be logged
 *		(regardless of its duration).
 *
 * Returns:
 *		0 if no logging is needed
 *		1 if just the duration should be logged
 *		2 if duration and query details should be logged
 *
 * If logging is needed, the duration in msec is formatted into msec_str[],
 * which must be a 32-byte buffer.
 *
 * was_logged should be true if caller already logged query details (this
 * essentially prevents 2 from being returned).
 */
int
check_log_duration(char *msec_str, bool was_logged)
{
	if (log_duration || log_min_duration_statement >= 0 || xact_is_sampled)
	{
		long		secs;
		int			usecs;
		int			msecs;
		bool		exceeded;

		TimestampDifference(GetCurrentStatementStartTimestamp(),
							GetCurrentTimestamp(),
							&secs, &usecs);
		msecs = usecs / 1000;

		/*
		 * This odd-looking test for log_min_duration_statement being exceeded
		 * is designed to avoid integer overflow with very long durations:
		 * don't compute secs * 1000 until we've verified it will fit in int.
		 */
		exceeded = (log_min_duration_statement == 0 ||
					(log_min_duration_statement > 0 &&
					 (secs > log_min_duration_statement / 1000 ||
					  secs * 1000 + msecs >= log_min_duration_statement)));

		if (exceeded || log_duration || xact_is_sampled)
		{
			snprintf(msec_str, 32, "%ld.%03d",
					 secs * 1000 + msecs, usecs % 1000);
			if ((exceeded || xact_is_sampled) && !was_logged)
				return 2;
			else
				return 1;
		}
	}

	return 0;
}

/*
 * errdetail_execute
 *
 * Add an errdetail() line showing the query referenced by an EXECUTE, if any.
 * The argument is the raw parsetree list.
 */
static int
errdetail_execute(List *raw_parsetree_list)
{
	ListCell   *parsetree_item;

	foreach(parsetree_item, raw_parsetree_list)
	{
		RawStmt    *parsetree = lfirst_node(RawStmt, parsetree_item);

		if (IsA(parsetree->stmt, ExecuteStmt))
		{
			ExecuteStmt *stmt = (ExecuteStmt *) parsetree->stmt;
			PreparedStatement *pstmt;

			pstmt = FetchPreparedStatement(stmt->name, false);
			if (pstmt)
			{
				errdetail("prepare: %s", pstmt->plansource->query_string);
				return 0;
			}
		}
	}

	return 0;
}

/*
 * errdetail_params
 *
 * Add an errdetail() line showing bind-parameter data, if available.
 */
static int
errdetail_params(ParamListInfo params)
{
	/* We mustn't call user-defined I/O functions when in an aborted xact */
	if (params && params->numParams > 0 && !IsAbortedTransactionBlockState())
	{
		StringInfoData param_str;
		MemoryContext oldcontext;

		/* This code doesn't support dynamic param lists */
		Assert(params->paramFetch == NULL);

		/* Make sure any trash is generated in MessageContext */
		oldcontext = MemoryContextSwitchTo(MessageContext);

		initStringInfo(&param_str);

		for (int paramno = 0; paramno < params->numParams; paramno++)
		{
			ParamExternData *prm = &params->params[paramno];
			Oid			typoutput;
			bool		typisvarlena;
			char	   *pstring;
			char	   *p;

			appendStringInfo(&param_str, "%s$%d = ",
							 paramno > 0 ? ", " : "",
							 paramno + 1);

			if (prm->isnull || !OidIsValid(prm->ptype))
			{
				appendStringInfoString(&param_str, "NULL");
				continue;
			}

			getTypeOutputInfo(prm->ptype, &typoutput, &typisvarlena);

			pstring = OidOutputFunctionCall(typoutput, prm->value);

			appendStringInfoCharMacro(&param_str, '\'');
			for (p = pstring; *p; p++)
			{
				if (*p == '\'') /* double single quotes */
					appendStringInfoCharMacro(&param_str, *p);
				appendStringInfoCharMacro(&param_str, *p);
			}
			appendStringInfoCharMacro(&param_str, '\'');

			pfree(pstring);
		}

		errdetail("parameters: %s", param_str.data);

		pfree(param_str.data);

		MemoryContextSwitchTo(oldcontext);
	}

	return 0;
}

/*
 * errdetail_abort
 *
 * Add an errdetail() line showing abort reason, if any.
 */
static int
errdetail_abort(void)
{
	if (MyProc->recoveryConflictPending)
		errdetail("abort reason: recovery conflict");

	return 0;
}

/*
 * errdetail_recovery_conflict
 *
 * Add an errdetail() line showing conflict source.
 */
static int
errdetail_recovery_conflict(void)
{
	switch (RecoveryConflictReason)
	{
		case PROCSIG_RECOVERY_CONFLICT_BUFFERPIN:
			errdetail("User was holding shared buffer pin for too long.");
			break;
		case PROCSIG_RECOVERY_CONFLICT_LOCK:
			errdetail("User was holding a relation lock for too long.");
			break;
		case PROCSIG_RECOVERY_CONFLICT_TABLESPACE:
			errdetail("User was or might have been using tablespace that must be dropped.");
			break;
		case PROCSIG_RECOVERY_CONFLICT_SNAPSHOT:
			errdetail("User query might have needed to see row versions that must be removed.");
			break;
		case PROCSIG_RECOVERY_CONFLICT_STARTUP_DEADLOCK:
			errdetail("User transaction caused buffer deadlock with recovery.");
			break;
		case PROCSIG_RECOVERY_CONFLICT_DATABASE:
			errdetail("User was connected to a database that must be dropped.");
			break;
		default:
			break;
			/* no errdetail */
	}

	return 0;
}

/*
 * exec_describe_statement_message
 *
 * Process a "Describe" message for a prepared statement
 */
static void
exec_describe_statement_message(const char *stmt_name)
{
	CachedPlanSource *psrc;

	/*
	 * Start up a transaction command. (Note that this will normally change
	 * current memory context.) Nothing happens if we are already in one.
	 */
	start_xact_command();

	/* Switch back to message context */
	MemoryContextSwitchTo(MessageContext);

	/* Find prepared statement */
	if (stmt_name[0] != '\0')
	{
		PreparedStatement *pstmt;

		pstmt = FetchPreparedStatement(stmt_name, true);
		psrc = pstmt->plansource;
	}
	else
	{
		/* special-case the unnamed statement */
		psrc = unnamed_stmt_psrc;
		if (!psrc)
			ereport(ERROR,
					(errcode(ERRCODE_UNDEFINED_PSTATEMENT),
					 errmsg("unnamed prepared statement does not exist")));
	}

	/* Prepared statements shouldn't have changeable result descs */
	Assert(psrc->fixed_result);

	/*
	 * If we are in aborted transaction state, we can't run
	 * SendRowDescriptionMessage(), because that needs catalog accesses.
	 * Hence, refuse to Describe statements that return data.  (We shouldn't
	 * just refuse all Describes, since that might break the ability of some
	 * clients to issue COMMIT or ROLLBACK commands, if they use code that
	 * blindly Describes whatever it does.)  We can Describe parameters
	 * without doing anything dangerous, so we don't restrict that.
	 */
	if (IsAbortedTransactionBlockState() &&
		psrc->resultDesc)
		ereport(ERROR,
				(errcode(ERRCODE_IN_FAILED_SQL_TRANSACTION),
				 errmsg("current transaction is aborted, "
						"commands ignored until end of transaction block"),
				 errdetail_abort()));

	if (whereToSendOutput != DestRemote)
		return;					/* can't actually do anything... */

	/*
	 * First describe the parameters...
	 */
	pq_beginmessage_reuse(&row_description_buf, 't');	/* parameter description
														 * message type */
	pq_sendint16(&row_description_buf, psrc->num_params);

	for (int i = 0; i < psrc->num_params; i++)
	{
		Oid			ptype = psrc->param_types[i];

		pq_sendint32(&row_description_buf, (int) ptype);
	}
	pq_endmessage_reuse(&row_description_buf);

	/*
	 * Next send RowDescription or NoData to describe the result...
	 */
	if (psrc->resultDesc)
	{
		List	   *tlist;

		/* Get the plan's primary targetlist */
		tlist = CachedPlanGetTargetList(psrc, NULL);

		SendRowDescriptionMessage(&row_description_buf,
								  psrc->resultDesc,
								  tlist,
								  NULL);
	}
	else
		pq_putemptymessage('n');	/* NoData */

}

/*
 * exec_describe_portal_message
 *
 * Process a "Describe" message for a portal
 */
static void
exec_describe_portal_message(const char *portal_name)
{
	Portal		portal;

	/*
	 * Start up a transaction command. (Note that this will normally change
	 * current memory context.) Nothing happens if we are already in one.
	 */
	start_xact_command();

	/* Switch back to message context */
	MemoryContextSwitchTo(MessageContext);

	portal = GetPortalByName(portal_name);
	if (!PortalIsValid(portal))
		ereport(ERROR,
				(errcode(ERRCODE_UNDEFINED_CURSOR),
				 errmsg("portal \"%s\" does not exist", portal_name)));

	/*
	 * If we are in aborted transaction state, we can't run
	 * SendRowDescriptionMessage(), because that needs catalog accesses.
	 * Hence, refuse to Describe portals that return data.  (We shouldn't just
	 * refuse all Describes, since that might break the ability of some
	 * clients to issue COMMIT or ROLLBACK commands, if they use code that
	 * blindly Describes whatever it does.)
	 */
	if (IsAbortedTransactionBlockState() &&
		portal->tupDesc)
		ereport(ERROR,
				(errcode(ERRCODE_IN_FAILED_SQL_TRANSACTION),
				 errmsg("current transaction is aborted, "
						"commands ignored until end of transaction block"),
				 errdetail_abort()));

	if (whereToSendOutput != DestRemote)
		return;					/* can't actually do anything... */

	if (portal->tupDesc)
		SendRowDescriptionMessage(&row_description_buf,
								  portal->tupDesc,
								  FetchPortalTargetList(portal),
								  portal->formats);
	else
		pq_putemptymessage('n');	/* NoData */
}


/*
 * Convenience routines for starting/committing a single command.
 */
static void
start_xact_command(void)
{
	if (!xact_started)
	{
		StartTransactionCommand();

		xact_started = true;
	}

	/*
	 * Start statement timeout if necessary.  Note that this'll intentionally
	 * not reset the clock on an already started timeout, to avoid the timing
	 * overhead when start_xact_command() is invoked repeatedly, without an
	 * interceding finish_xact_command() (e.g. parse/bind/execute).  If that's
	 * not desired, the timeout has to be disabled explicitly.
	 */
	enable_statement_timeout();
}

static void
finish_xact_command(void)
{
	/* cancel active statement timeout after each command */
	disable_statement_timeout();

	if (xact_started)
	{
		CommitTransactionCommand();

#ifdef MEMORY_CONTEXT_CHECKING
		/* Check all memory contexts that weren't freed during commit */
		/* (those that were, were checked before being deleted) */
		MemoryContextCheck(TopMemoryContext);
#endif

#ifdef SHOW_MEMORY_STATS
		/* Print mem stats after each commit for leak tracking */
		MemoryContextStats(TopMemoryContext);
#endif

		xact_started = false;
	}
}


/*
 * Convenience routines for checking whether a statement is one of the
 * ones that we allow in transaction-aborted state.
 */

/* Test a bare parsetree */
static bool
IsTransactionExitStmt(Node *parsetree)
{
	if (parsetree && IsA(parsetree, TransactionStmt))
	{
		TransactionStmt *stmt = (TransactionStmt *) parsetree;

		if (stmt->kind == TRANS_STMT_COMMIT ||
			stmt->kind == TRANS_STMT_PREPARE ||
			stmt->kind == TRANS_STMT_ROLLBACK ||
			stmt->kind == TRANS_STMT_ROLLBACK_TO)
			return true;
	}
	return false;
}

/* Test a list that contains PlannedStmt nodes */
static bool
IsTransactionExitStmtList(List *pstmts)
{
	if (list_length(pstmts) == 1)
	{
		PlannedStmt *pstmt = linitial_node(PlannedStmt, pstmts);

		if (pstmt->commandType == CMD_UTILITY &&
			IsTransactionExitStmt(pstmt->utilityStmt))
			return true;
	}
	return false;
}

/* Test a list that contains PlannedStmt nodes */
static bool
IsTransactionStmtList(List *pstmts)
{
	if (list_length(pstmts) == 1)
	{
		PlannedStmt *pstmt = linitial_node(PlannedStmt, pstmts);

		if (pstmt->commandType == CMD_UTILITY &&
			IsA(pstmt->utilityStmt, TransactionStmt))
			return true;
	}
	return false;
}

/* Release any existing unnamed prepared statement */
static void
drop_unnamed_stmt(void)
{
	/* paranoia to avoid a dangling pointer in case of error */
	if (unnamed_stmt_psrc)
	{
		CachedPlanSource *psrc = unnamed_stmt_psrc;

		unnamed_stmt_psrc = NULL;
		DropCachedPlan(psrc);
	}
}


/* --------------------------------
 *		signal handler routines used in PostgresMain()
 * --------------------------------
 */

/*
 * quickdie() occurs when signalled SIGQUIT by the postmaster.
 *
 * Some backend has bought the farm,
 * so we need to stop what we're doing and exit.
 */
void
quickdie(SIGNAL_ARGS)
{
	sigaddset(&BlockSig, SIGQUIT);	/* prevent nested calls */
	PG_SETMASK(&BlockSig);

	/*
	 * Prevent interrupts while exiting; though we just blocked signals that
	 * would queue new interrupts, one may have been pending.  We don't want a
	 * quickdie() downgraded to a mere query cancel.
	 */
	HOLD_INTERRUPTS();

	/*
	 * If we're aborting out of client auth, don't risk trying to send
	 * anything to the client; we will likely violate the protocol, not to
	 * mention that we may have interrupted the guts of OpenSSL or some
	 * authentication library.
	 */
	if (ClientAuthInProgress && whereToSendOutput == DestRemote)
		whereToSendOutput = DestNone;

	/*
	 * Notify the client before exiting, to give a clue on what happened.
	 *
	 * It's dubious to call ereport() from a signal handler.  It is certainly
	 * not async-signal safe.  But it seems better to try, than to disconnect
	 * abruptly and leave the client wondering what happened.  It's remotely
	 * possible that we crash or hang while trying to send the message, but
	 * receiving a SIGQUIT is a sign that something has already gone badly
	 * wrong, so there's not much to lose.  Assuming the postmaster is still
	 * running, it will SIGKILL us soon if we get stuck for some reason.
	 *
	 * Ideally this should be ereport(FATAL), but then we'd not get control
	 * back...
	 */
	ereport(WARNING,
			(errcode(ERRCODE_CRASH_SHUTDOWN),
			 errmsg("terminating connection because of crash of another server process"),
			 errdetail("The postmaster has commanded this server process to roll back"
					   " the current transaction and exit, because another"
					   " server process exited abnormally and possibly corrupted"
					   " shared memory."),
			 errhint("In a moment you should be able to reconnect to the"
					 " database and repeat your command.")));

	/*
	 * We DO NOT want to run proc_exit() or atexit() callbacks -- we're here
	 * because shared memory may be corrupted, so we don't want to try to
	 * clean up our transaction.  Just nail the windows shut and get out of
	 * town.  The callbacks wouldn't be safe to run from a signal handler,
	 * anyway.
	 *
	 * Note we do _exit(2) not _exit(0).  This is to force the postmaster into
	 * a system reset cycle if someone sends a manual SIGQUIT to a random
	 * backend.  This is necessary precisely because we don't clean up our
	 * shared memory state.  (The "dead man switch" mechanism in pmsignal.c
	 * should ensure the postmaster sees this as a crash, too, but no harm in
	 * being doubly sure.)
	 */
	_exit(2);
}

/*
 * Shutdown signal from postmaster: abort transaction and exit
 * at soonest convenient time
 */
void
die(SIGNAL_ARGS)
{
	int			save_errno = errno;

	/* Don't joggle the elbow of proc_exit */
	if (!proc_exit_inprogress)
	{
		InterruptPending = true;
		ProcDiePending = true;
	}

	/* If we're still here, waken anything waiting on the process latch */
	SetLatch(MyLatch);

	/*
	 * If we're in single user mode, we want to quit immediately - we can't
	 * rely on latches as they wouldn't work when stdin/stdout is a file.
	 * Rather ugly, but it's unlikely to be worthwhile to invest much more
	 * effort just for the benefit of single user mode.
	 */
	if (DoingCommandRead && whereToSendOutput != DestRemote)
		ProcessInterrupts();

	errno = save_errno;
}

/*
 * Query-cancel signal from postmaster: abort current transaction
 * at soonest convenient time
 */
void
StatementCancelHandler(SIGNAL_ARGS)
{
	int			save_errno = errno;

	/*
	 * Don't joggle the elbow of proc_exit
	 */
	if (!proc_exit_inprogress)
	{
		InterruptPending = true;
		QueryCancelPending = true;
	}

	/* If we're still here, waken anything waiting on the process latch */
	SetLatch(MyLatch);

	errno = save_errno;
}

/* signal handler for floating point exception */
void
FloatExceptionHandler(SIGNAL_ARGS)
{
	/* We're not returning, so no need to save errno */
	ereport(ERROR,
			(errcode(ERRCODE_FLOATING_POINT_EXCEPTION),
			 errmsg("floating-point exception"),
			 errdetail("An invalid floating-point operation was signaled. "
					   "This probably means an out-of-range result or an "
					   "invalid operation, such as division by zero.")));
}

/*
 * SIGHUP: set flag to re-read config file at next convenient time.
 *
 * Sets the ConfigReloadPending flag, which should be checked at convenient
 * places inside main loops. (Better than doing the reading in the signal
 * handler, ey?)
 */
void
PostgresSigHupHandler(SIGNAL_ARGS)
{
	int			save_errno = errno;

	ConfigReloadPending = true;
	SetLatch(MyLatch);

	errno = save_errno;
}

/*
 * RecoveryConflictInterrupt: out-of-line portion of recovery conflict
 * handling following receipt of SIGUSR1. Designed to be similar to die()
 * and StatementCancelHandler(). Called only by a normal user backend
 * that begins a transaction during recovery.
 */
void
RecoveryConflictInterrupt(ProcSignalReason reason)
{
	int			save_errno = errno;

	/*
	 * Don't joggle the elbow of proc_exit
	 */
	if (!proc_exit_inprogress)
	{
		RecoveryConflictReason = reason;
		switch (reason)
		{
			case PROCSIG_RECOVERY_CONFLICT_STARTUP_DEADLOCK:

				/*
				 * If we aren't waiting for a lock we can never deadlock.
				 */
				if (!IsWaitingForLock())
					return;

				/* Intentional fall through to check wait for pin */
				/* FALLTHROUGH */

			case PROCSIG_RECOVERY_CONFLICT_BUFFERPIN:

				/*
				 * If PROCSIG_RECOVERY_CONFLICT_BUFFERPIN is requested but we
				 * aren't blocking the Startup process there is nothing more
				 * to do.
				 *
				 * When PROCSIG_RECOVERY_CONFLICT_STARTUP_DEADLOCK is
				 * requested, if we're waiting for locks and the startup
				 * process is not waiting for buffer pin (i.e., also waiting
				 * for locks), we set the flag so that ProcSleep() will check
				 * for deadlocks.
				 */
				if (!HoldingBufferPinThatDelaysRecovery())
				{
					if (reason == PROCSIG_RECOVERY_CONFLICT_STARTUP_DEADLOCK &&
						GetStartupBufferPinWaitBufId() < 0)
						CheckDeadLockAlert();
					return;
				}

				MyProc->recoveryConflictPending = true;

				/* Intentional fall through to error handling */
				/* FALLTHROUGH */

			case PROCSIG_RECOVERY_CONFLICT_LOCK:
			case PROCSIG_RECOVERY_CONFLICT_TABLESPACE:
			case PROCSIG_RECOVERY_CONFLICT_SNAPSHOT:

				/*
				 * If we aren't in a transaction any longer then ignore.
				 */
				if (!IsTransactionOrTransactionBlock())
					return;

				/*
				 * If we can abort just the current subtransaction then we are
				 * OK to throw an ERROR to resolve the conflict. Otherwise
				 * drop through to the FATAL case.
				 *
				 * XXX other times that we can throw just an ERROR *may* be
				 * PROCSIG_RECOVERY_CONFLICT_LOCK if no locks are held in
				 * parent transactions
				 *
				 * PROCSIG_RECOVERY_CONFLICT_SNAPSHOT if no snapshots are held
				 * by parent transactions and the transaction is not
				 * transaction-snapshot mode
				 *
				 * PROCSIG_RECOVERY_CONFLICT_TABLESPACE if no temp files or
				 * cursors open in parent transactions
				 */
				if (!IsSubTransaction())
				{
					/*
					 * If we already aborted then we no longer need to cancel.
					 * We do this here since we do not wish to ignore aborted
					 * subtransactions, which must cause FATAL, currently.
					 */
					if (IsAbortedTransactionBlockState())
						return;

					RecoveryConflictPending = true;
					QueryCancelPending = true;
					InterruptPending = true;
					break;
				}

				/* Intentional fall through to session cancel */
				/* FALLTHROUGH */

			case PROCSIG_RECOVERY_CONFLICT_DATABASE:
				RecoveryConflictPending = true;
				ProcDiePending = true;
				InterruptPending = true;
				break;

			default:
				elog(FATAL, "unrecognized conflict mode: %d",
					 (int) reason);
		}

		Assert(RecoveryConflictPending && (QueryCancelPending || ProcDiePending));

		/*
		 * All conflicts apart from database cause dynamic errors where the
		 * command or transaction can be retried at a later point with some
		 * potential for success. No need to reset this, since non-retryable
		 * conflict errors are currently FATAL.
		 */
		if (reason == PROCSIG_RECOVERY_CONFLICT_DATABASE)
			RecoveryConflictRetryable = false;
	}

	/*
	 * Set the process latch. This function essentially emulates signal
	 * handlers like die() and StatementCancelHandler() and it seems prudent
	 * to behave similarly as they do.
	 */
	SetLatch(MyLatch);

	errno = save_errno;
}

/*
 * ProcessInterrupts: out-of-line portion of CHECK_FOR_INTERRUPTS() macro
 *
 * If an interrupt condition is pending, and it's safe to service it,
 * then clear the flag and accept the interrupt.  Called only when
 * InterruptPending is true.
 */
void
ProcessInterrupts(void)
{
	/* OK to accept any interrupts now? */
	if (InterruptHoldoffCount != 0 || CritSectionCount != 0)
		return;
	InterruptPending = false;

	if (ProcDiePending)
	{
		ProcDiePending = false;
		QueryCancelPending = false; /* ProcDie trumps QueryCancel */
		LockErrorCleanup();
		/* As in quickdie, don't risk sending to client during auth */
		if (ClientAuthInProgress && whereToSendOutput == DestRemote)
			whereToSendOutput = DestNone;
		if (ClientAuthInProgress)
			ereport(FATAL,
					(errcode(ERRCODE_QUERY_CANCELED),
					 errmsg("canceling authentication due to timeout")));
		else if (IsAutoVacuumWorkerProcess())
			ereport(FATAL,
					(errcode(ERRCODE_ADMIN_SHUTDOWN),
					 errmsg("terminating autovacuum process due to administrator command")));
		else if (IsLogicalWorker())
			ereport(FATAL,
					(errcode(ERRCODE_ADMIN_SHUTDOWN),
					 errmsg("terminating logical replication worker due to administrator command")));
		else if (IsLogicalLauncher())
		{
			ereport(DEBUG1,
					(errmsg("logical replication launcher shutting down")));

			/*
			 * The logical replication launcher can be stopped at any time.
			 * Use exit status 1 so the background worker is restarted.
			 */
			proc_exit(1);
		}
		else if (RecoveryConflictPending && RecoveryConflictRetryable)
		{
			pgstat_report_recovery_conflict(RecoveryConflictReason);
			ereport(FATAL,
					(errcode(ERRCODE_T_R_SERIALIZATION_FAILURE),
					 errmsg("terminating connection due to conflict with recovery"),
					 errdetail_recovery_conflict()));
		}
		else if (RecoveryConflictPending)
		{
			/* Currently there is only one non-retryable recovery conflict */
			Assert(RecoveryConflictReason == PROCSIG_RECOVERY_CONFLICT_DATABASE);
			pgstat_report_recovery_conflict(RecoveryConflictReason);
			ereport(FATAL,
					(errcode(ERRCODE_DATABASE_DROPPED),
					 errmsg("terminating connection due to conflict with recovery"),
					 errdetail_recovery_conflict()));
		}
		else
			ereport(FATAL,
					(errcode(ERRCODE_ADMIN_SHUTDOWN),
					 errmsg("terminating connection due to administrator command")));
	}
	if (ClientConnectionLost)
	{
		QueryCancelPending = false; /* lost connection trumps QueryCancel */
		LockErrorCleanup();
		/* don't send to client, we already know the connection to be dead. */
		whereToSendOutput = DestNone;
		ereport(FATAL,
				(errcode(ERRCODE_CONNECTION_FAILURE),
				 errmsg("connection to client lost")));
	}

	/*
	 * If a recovery conflict happens while we are waiting for input from the
	 * client, the client is presumably just sitting idle in a transaction,
	 * preventing recovery from making progress.  Terminate the connection to
	 * dislodge it.
	 */
	if (RecoveryConflictPending && DoingCommandRead)
	{
		QueryCancelPending = false; /* this trumps QueryCancel */
		RecoveryConflictPending = false;
		LockErrorCleanup();
		pgstat_report_recovery_conflict(RecoveryConflictReason);
		ereport(FATAL,
				(errcode(ERRCODE_T_R_SERIALIZATION_FAILURE),
				 errmsg("terminating connection due to conflict with recovery"),
				 errdetail_recovery_conflict(),
				 errhint("In a moment you should be able to reconnect to the"
						 " database and repeat your command.")));
	}

	/*
	 * Don't allow query cancel interrupts while reading input from the
	 * client, because we might lose sync in the FE/BE protocol.  (Die
	 * interrupts are OK, because we won't read any further messages from the
	 * client in that case.)
	 */
	if (QueryCancelPending && QueryCancelHoldoffCount != 0)
	{
		/*
		 * Re-arm InterruptPending so that we process the cancel request as
		 * soon as we're done reading the message.
		 */
		InterruptPending = true;
	}
	else if (QueryCancelPending)
	{
		bool		lock_timeout_occurred;
		bool		stmt_timeout_occurred;

		QueryCancelPending = false;

		/*
		 * If LOCK_TIMEOUT and STATEMENT_TIMEOUT indicators are both set, we
		 * need to clear both, so always fetch both.
		 */
		lock_timeout_occurred = get_timeout_indicator(LOCK_TIMEOUT, true);
		stmt_timeout_occurred = get_timeout_indicator(STATEMENT_TIMEOUT, true);

		/*
		 * If both were set, we want to report whichever timeout completed
		 * earlier; this ensures consistent behavior if the machine is slow
		 * enough that the second timeout triggers before we get here.  A tie
		 * is arbitrarily broken in favor of reporting a lock timeout.
		 */
		if (lock_timeout_occurred && stmt_timeout_occurred &&
			get_timeout_finish_time(STATEMENT_TIMEOUT) < get_timeout_finish_time(LOCK_TIMEOUT))
			lock_timeout_occurred = false;	/* report stmt timeout */

		if (lock_timeout_occurred)
		{
			LockErrorCleanup();
			ereport(ERROR,
					(errcode(ERRCODE_LOCK_NOT_AVAILABLE),
					 errmsg("canceling statement due to lock timeout")));
		}
		if (stmt_timeout_occurred)
		{
			LockErrorCleanup();
			ereport(ERROR,
					(errcode(ERRCODE_QUERY_CANCELED),
					 errmsg("canceling statement due to statement timeout")));
		}
		if (IsAutoVacuumWorkerProcess())
		{
			LockErrorCleanup();
			ereport(ERROR,
					(errcode(ERRCODE_QUERY_CANCELED),
					 errmsg("canceling autovacuum task")));
		}
		if (RecoveryConflictPending)
		{
			RecoveryConflictPending = false;
			LockErrorCleanup();
			pgstat_report_recovery_conflict(RecoveryConflictReason);
			ereport(ERROR,
					(errcode(ERRCODE_T_R_SERIALIZATION_FAILURE),
					 errmsg("canceling statement due to conflict with recovery"),
					 errdetail_recovery_conflict()));
		}

		/*
		 * If we are reading a command from the client, just ignore the cancel
		 * request --- sending an extra error message won't accomplish
		 * anything.  Otherwise, go ahead and throw the error.
		 */
		if (!DoingCommandRead)
		{
			LockErrorCleanup();
			ereport(ERROR,
					(errcode(ERRCODE_QUERY_CANCELED),
					 errmsg("canceling statement due to user request")));
		}
	}

	if (IdleInTransactionSessionTimeoutPending)
	{
		/* Has the timeout setting changed since last we looked? */
		if (IdleInTransactionSessionTimeout > 0)
			ereport(FATAL,
					(errcode(ERRCODE_IDLE_IN_TRANSACTION_SESSION_TIMEOUT),
					 errmsg("terminating connection due to idle-in-transaction timeout")));
		else
			IdleInTransactionSessionTimeoutPending = false;

	}

	if (ParallelMessagePending)
		HandleParallelMessages();
}


/*
 * IA64-specific code to fetch the AR.BSP register for stack depth checks.
 *
 * We currently support gcc, icc, and HP-UX's native compiler here.
 *
 * Note: while icc accepts gcc asm blocks on x86[_64], this is not true on
 * ia64 (at least not in icc versions before 12.x).  So we have to carry a
 * separate implementation for it.
 */
#if defined(__ia64__) || defined(__ia64)

#if defined(__hpux) && !defined(__GNUC__) && !defined(__INTEL_COMPILER)
/* Assume it's HP-UX native compiler */
#include <ia64/sys/inline.h>
#define ia64_get_bsp() ((char *) (_Asm_mov_from_ar(_AREG_BSP, _NO_FENCE)))
#elif defined(__INTEL_COMPILER)
/* icc */
#include <asm/ia64regs.h>
#define ia64_get_bsp() ((char *) __getReg(_IA64_REG_AR_BSP))
#else
/* gcc */
static __inline__ char *
ia64_get_bsp(void)
{
	char	   *ret;

	/* the ;; is a "stop", seems to be required before fetching BSP */
	__asm__ __volatile__(
						 ";;\n"
						 "	mov	%0=ar.bsp	\n"
:						 "=r"(ret));

	return ret;
}
#endif
#endif							/* IA64 */


/*
 * set_stack_base: set up reference point for stack depth checking
 *
 * Returns the old reference point, if any.
 */
pg_stack_base_t
set_stack_base(void)
{
	char		stack_base;
	pg_stack_base_t old;

#if defined(__ia64__) || defined(__ia64)
	old.stack_base_ptr = stack_base_ptr;
	old.register_stack_base_ptr = register_stack_base_ptr;
#else
	old = stack_base_ptr;
#endif

	/* Set up reference point for stack depth checking */
	stack_base_ptr = &stack_base;
#if defined(__ia64__) || defined(__ia64)
	register_stack_base_ptr = ia64_get_bsp();
#endif

	return old;
}

/*
 * restore_stack_base: restore reference point for stack depth checking
 *
 * This can be used after set_stack_base() to restore the old value. This
 * is currently only used in PL/Java. When PL/Java calls a backend function
 * from different thread, the thread's stack is at a different location than
 * the main thread's stack, so it sets the base pointer before the call, and
 * restores it afterwards.
 */
void
restore_stack_base(pg_stack_base_t base)
{
#if defined(__ia64__) || defined(__ia64)
	stack_base_ptr = base.stack_base_ptr;
	register_stack_base_ptr = base.register_stack_base_ptr;
#else
	stack_base_ptr = base;
#endif
}

/*
 * check_stack_depth/stack_is_too_deep: check for excessively deep recursion
 *
 * This should be called someplace in any recursive routine that might possibly
 * recurse deep enough to overflow the stack.  Most Unixen treat stack
 * overflow as an unrecoverable SIGSEGV, so we want to error out ourselves
 * before hitting the hardware limit.
 *
 * check_stack_depth() just throws an error summarily.  stack_is_too_deep()
 * can be used by code that wants to handle the error condition itself.
 */
void
check_stack_depth(void)
{
	if (stack_is_too_deep())
	{
		ereport(ERROR,
				(errcode(ERRCODE_STATEMENT_TOO_COMPLEX),
				 errmsg("stack depth limit exceeded"),
				 errhint("Increase the configuration parameter \"max_stack_depth\" (currently %dkB), "
						 "after ensuring the platform's stack depth limit is adequate.",
						 max_stack_depth)));
	}
}

bool
stack_is_too_deep(void)
{
	char		stack_top_loc;
	long		stack_depth;

	/*
	 * Compute distance from reference point to my local variables
	 */
	stack_depth = (long) (stack_base_ptr - &stack_top_loc);

	/*
	 * Take abs value, since stacks grow up on some machines, down on others
	 */
	if (stack_depth < 0)
		stack_depth = -stack_depth;

	/*
	 * Trouble?
	 *
	 * The test on stack_base_ptr prevents us from erroring out if called
	 * during process setup or in a non-backend process.  Logically it should
	 * be done first, but putting it here avoids wasting cycles during normal
	 * cases.
	 */
	if (stack_depth > max_stack_depth_bytes &&
		stack_base_ptr != NULL)
		return true;

	/*
	 * On IA64 there is a separate "register" stack that requires its own
	 * independent check.  For this, we have to measure the change in the
	 * "BSP" pointer from PostgresMain to here.  Logic is just as above,
	 * except that we know IA64's register stack grows up.
	 *
	 * Note we assume that the same max_stack_depth applies to both stacks.
	 */
#if defined(__ia64__) || defined(__ia64)
	stack_depth = (long) (ia64_get_bsp() - register_stack_base_ptr);

	if (stack_depth > max_stack_depth_bytes &&
		register_stack_base_ptr != NULL)
		return true;
#endif							/* IA64 */

	return false;
}

/* GUC check hook for max_stack_depth */
bool
check_max_stack_depth(int *newval, void **extra, GucSource source)
{
	long		newval_bytes = *newval * 1024L;
	long		stack_rlimit = get_stack_depth_rlimit();

	if (stack_rlimit > 0 && newval_bytes > stack_rlimit - STACK_DEPTH_SLOP)
	{
		GUC_check_errdetail("\"max_stack_depth\" must not exceed %ldkB.",
							(stack_rlimit - STACK_DEPTH_SLOP) / 1024L);
		GUC_check_errhint("Increase the platform's stack depth limit via \"ulimit -s\" or local equivalent.");
		return false;
	}
	return true;
}

/* GUC assign hook for max_stack_depth */
void
assign_max_stack_depth(int newval, void *extra)
{
	long		newval_bytes = newval * 1024L;

	max_stack_depth_bytes = newval_bytes;
}


/*
 * set_debug_options --- apply "-d N" command line option
 *
 * -d is not quite the same as setting log_min_messages because it enables
 * other output options.
 */
void
set_debug_options(int debug_flag, GucContext context, GucSource source)
{
	if (debug_flag > 0)
	{
		char		debugstr[64];

		sprintf(debugstr, "debug%d", debug_flag);
		SetConfigOption("log_min_messages", debugstr, context, source);
	}
	else
		SetConfigOption("log_min_messages", "notice", context, source);

	if (debug_flag >= 1 && context == PGC_POSTMASTER)
	{
		SetConfigOption("log_connections", "true", context, source);
		SetConfigOption("log_disconnections", "true", context, source);
	}
	if (debug_flag >= 2)
		SetConfigOption("log_statement", "all", context, source);
	if (debug_flag >= 3)
		SetConfigOption("debug_print_parse", "true", context, source);
	if (debug_flag >= 4)
		SetConfigOption("debug_print_plan", "true", context, source);
	if (debug_flag >= 5)
		SetConfigOption("debug_print_rewritten", "true", context, source);
}


bool
set_plan_disabling_options(const char *arg, GucContext context, GucSource source)
{
	const char *tmp = NULL;

	switch (arg[0])
	{
		case 's':				/* seqscan */
			tmp = "enable_seqscan";
			break;
		case 'i':				/* indexscan */
			tmp = "enable_indexscan";
			break;
		case 'o':				/* indexonlyscan */
			tmp = "enable_indexonlyscan";
			break;
		case 'b':				/* bitmapscan */
			tmp = "enable_bitmapscan";
			break;
		case 't':				/* tidscan */
			tmp = "enable_tidscan";
			break;
		case 'n':				/* nestloop */
			tmp = "enable_nestloop";
			break;
		case 'm':				/* mergejoin */
			tmp = "enable_mergejoin";
			break;
		case 'h':				/* hashjoin */
			tmp = "enable_hashjoin";
			break;
	}
	if (tmp)
	{
		SetConfigOption(tmp, "false", context, source);
		return true;
	}
	else
		return false;
}


const char *
get_stats_option_name(const char *arg)
{
	switch (arg[0])
	{
		case 'p':
			if (optarg[1] == 'a')	/* "parser" */
				return "log_parser_stats";
			else if (optarg[1] == 'l')	/* "planner" */
				return "log_planner_stats";
			break;

		case 'e':				/* "executor" */
			return "log_executor_stats";
			break;
	}

	return NULL;
}


/* ----------------------------------------------------------------
 * process_postgres_switches
 *	   Parse command line arguments for PostgresMain
 *
 * This is called twice, once for the "secure" options coming from the
 * postmaster or command line, and once for the "insecure" options coming
 * from the client's startup packet.  The latter have the same syntax but
 * may be restricted in what they can do.
 *
 * argv[0] is ignored in either case (it's assumed to be the program name).
 *
 * ctx is PGC_POSTMASTER for secure options, PGC_BACKEND for insecure options
 * coming from the client, or PGC_SU_BACKEND for insecure options coming from
 * a superuser client.
 *
 * If a database name is present in the command line arguments, it's
 * returned into *dbname (this is allowed only if *dbname is initially NULL).
 * ----------------------------------------------------------------
 */
void
process_postgres_switches(int argc, char *argv[], GucContext ctx,
						  const char **dbname)
{
	bool		secure = (ctx == PGC_POSTMASTER);
	int			errs = 0;
	GucSource	gucsource;
	int			flag;

	if (secure)
	{
		gucsource = PGC_S_ARGV; /* switches came from command line */

		/* Ignore the initial --single argument, if present */
		if (argc > 1 && strcmp(argv[1], "--single") == 0)
		{
			argv++;
			argc--;
		}
	}
	else
	{
		gucsource = PGC_S_CLIENT;	/* switches came from client */
	}

#ifdef HAVE_INT_OPTERR

	/*
	 * Turn this off because it's either printed to stderr and not the log
	 * where we'd want it, or argv[0] is now "--single", which would make for
	 * a weird error message.  We print our own error message below.
	 */
	opterr = 0;
#endif

	/*
	 * Parse command-line options.  CAUTION: keep this in sync with
	 * postmaster/postmaster.c (the option sets should not conflict) and with
	 * the common help() function in main/main.c.
	 */
	while ((flag = getopt(argc, argv, "B:bc:C:D:d:EeFf:h:ijk:lN:nOo:Pp:r:S:sTt:v:W:-:")) != -1)
	{
		switch (flag)
		{
			case 'B':
				SetConfigOption("shared_buffers", optarg, ctx, gucsource);
				break;

			case 'b':
				/* Undocumented flag used for binary upgrades */
				if (secure)
					IsBinaryUpgrade = true;
				break;

			case 'C':
				/* ignored for consistency with the postmaster */
				break;

			case 'D':
				if (secure)
					userDoption = strdup(optarg);
				break;

			case 'd':
				set_debug_options(atoi(optarg), ctx, gucsource);
				break;

			case 'E':
				if (secure)
					EchoQuery = true;
				break;

			case 'e':
				SetConfigOption("datestyle", "euro", ctx, gucsource);
				break;

			case 'F':
				SetConfigOption("fsync", "false", ctx, gucsource);
				break;

			case 'f':
				if (!set_plan_disabling_options(optarg, ctx, gucsource))
					errs++;
				break;

			case 'h':
				SetConfigOption("listen_addresses", optarg, ctx, gucsource);
				break;

			case 'i':
				SetConfigOption("listen_addresses", "*", ctx, gucsource);
				break;

			case 'j':
				if (secure)
					UseSemiNewlineNewline = true;
				break;

			case 'k':
				SetConfigOption("unix_socket_directories", optarg, ctx, gucsource);
				break;

			case 'l':
				SetConfigOption("ssl", "true", ctx, gucsource);
				break;

			case 'N':
				SetConfigOption("max_connections", optarg, ctx, gucsource);
				break;

			case 'n':
				/* ignored for consistency with postmaster */
				break;

			case 'O':
				SetConfigOption("allow_system_table_mods", "true", ctx, gucsource);
				break;

			case 'o':
				errs++;
				break;

			case 'P':
				SetConfigOption("ignore_system_indexes", "true", ctx, gucsource);
				break;

			case 'p':
				SetConfigOption("port", optarg, ctx, gucsource);
				break;

			case 'r':
				/* send output (stdout and stderr) to the given file */
				if (secure)
					strlcpy(OutputFileName, optarg, MAXPGPATH);
				break;

			case 'S':
				SetConfigOption("work_mem", optarg, ctx, gucsource);
				break;

			case 's':
				SetConfigOption("log_statement_stats", "true", ctx, gucsource);
				break;

			case 'T':
				/* ignored for consistency with the postmaster */
				break;

			case 't':
				{
					const char *tmp = get_stats_option_name(optarg);

					if (tmp)
						SetConfigOption(tmp, "true", ctx, gucsource);
					else
						errs++;
					break;
				}

			case 'v':

				/*
				 * -v is no longer used in normal operation, since
				 * FrontendProtocol is already set before we get here. We keep
				 * the switch only for possible use in standalone operation,
				 * in case we ever support using normal FE/BE protocol with a
				 * standalone backend.
				 */
				if (secure)
					FrontendProtocol = (ProtocolVersion) atoi(optarg);
				break;

			case 'W':
				SetConfigOption("post_auth_delay", optarg, ctx, gucsource);
				break;

			case 'c':
			case '-':
				{
					char	   *name,
							   *value;

					ParseLongOption(optarg, &name, &value);
					if (!value)
					{
						if (flag == '-')
							ereport(ERROR,
									(errcode(ERRCODE_SYNTAX_ERROR),
									 errmsg("--%s requires a value",
											optarg)));
						else
							ereport(ERROR,
									(errcode(ERRCODE_SYNTAX_ERROR),
									 errmsg("-c %s requires a value",
											optarg)));
					}
					SetConfigOption(name, value, ctx, gucsource);
					free(name);
					if (value)
						free(value);
					break;
				}

			default:
				errs++;
				break;
		}

		if (errs)
			break;
	}

	/*
	 * Optional database name should be there only if *dbname is NULL.
	 */
	if (!errs && dbname && *dbname == NULL && argc - optind >= 1)
		*dbname = strdup(argv[optind++]);

	if (errs || argc != optind)
	{
		if (errs)
			optind--;			/* complain about the previous argument */

		/* spell the error message a bit differently depending on context */
		if (IsUnderPostmaster)
			ereport(FATAL,
					errcode(ERRCODE_SYNTAX_ERROR),
					errmsg("invalid command-line argument for server process: %s", argv[optind]),
					errhint("Try \"%s --help\" for more information.", progname));
		else
			ereport(FATAL,
					errcode(ERRCODE_SYNTAX_ERROR),
					errmsg("%s: invalid command-line argument: %s",
						   progname, argv[optind]),
					errhint("Try \"%s --help\" for more information.", progname));
	}

	/*
	 * Reset getopt(3) library so that it will work correctly in subprocesses
	 * or when this function is called a second time with another array.
	 */
	optind = 1;
#ifdef HAVE_INT_OPTRESET
	optreset = 1;				/* some systems need this too */
#endif
}


/* ----------------------------------------------------------------
 * PostgresMain
 *	   postgres main loop -- all backends, interactive or otherwise start here
 *
 * argc/argv are the command line arguments to be used.  (When being forked
 * by the postmaster, these are not the original argv array of the process.)
 * dbname is the name of the database to connect to, or NULL if the database
 * name should be extracted from the command line arguments or defaulted.
 * username is the PostgreSQL user name to be used for the session.
 * ----------------------------------------------------------------
 */
void
PostgresMain(int argc, char *argv[],
			 const char *dbname,
			 const char *username)
{
	printf("\n -- PostgresMain -- \n");
	int			firstchar;
	StringInfoData input_message;
	sigjmp_buf	local_sigjmp_buf;
	volatile bool send_ready_for_query = true;
	bool		disable_idle_in_transaction_timeout = false;

	/* Initialize startup process environment if necessary. */
	if (!IsUnderPostmaster)
		InitStandaloneProcess(argv[0]);

	SetProcessingMode(InitProcessing);

	/*
	 * Set default values for command-line options.
	 */
	if (!IsUnderPostmaster)
		InitializeGUCOptions();

	/*
	 * Parse command-line options.
	 */
	process_postgres_switches(argc, argv, PGC_POSTMASTER, &dbname);

	/* Must have gotten a database name, or have a default (the username) */
	if (dbname == NULL)
	{
		dbname = username;
		if (dbname == NULL)
			ereport(FATAL,
					(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
					 errmsg("%s: no database nor user name specified",
							progname)));
	}

	/* Acquire configuration parameters, unless inherited from postmaster */
	if (!IsUnderPostmaster)
	{
		if (!SelectConfigFiles(userDoption, progname))
			proc_exit(1);
	}

	/*
	 * Set up signal handlers and masks.
	 *
	 * Note that postmaster blocked all signals before forking child process,
	 * so there is no race condition whereby we might receive a signal before
	 * we have set up the handler.
	 *
	 * Also note: it's best not to use any signals that are SIG_IGNored in the
	 * postmaster.  If such a signal arrives before we are able to change the
	 * handler to non-SIG_IGN, it'll get dropped.  Instead, make a dummy
	 * handler in the postmaster to reserve the signal. (Of course, this isn't
	 * an issue for signals that are locally generated, such as SIGALRM and
	 * SIGPIPE.)
	 */
	if (am_walsender)
		WalSndSignals();
	else
	{
		pqsignal(SIGHUP, PostgresSigHupHandler);	/* set flag to read config
													 * file */
		pqsignal(SIGINT, StatementCancelHandler);	/* cancel current query */
		pqsignal(SIGTERM, die); /* cancel current query and exit */

		/*
		 * In a standalone backend, SIGQUIT can be generated from the keyboard
		 * easily, while SIGTERM cannot, so we make both signals do die()
		 * rather than quickdie().
		 */
		if (IsUnderPostmaster)
			pqsignal(SIGQUIT, quickdie);	/* hard crash time */
		else
			pqsignal(SIGQUIT, die); /* cancel current query and exit */
		InitializeTimeouts();	/* establishes SIGALRM handler */

		/*
		 * Ignore failure to write to frontend. Note: if frontend closes
		 * connection, we will notice it and exit cleanly when control next
		 * returns to outer loop.  This seems safer than forcing exit in the
		 * midst of output during who-knows-what operation...
		 */
		pqsignal(SIGPIPE, SIG_IGN);
		pqsignal(SIGUSR1, procsignal_sigusr1_handler);
		pqsignal(SIGUSR2, SIG_IGN);
		pqsignal(SIGFPE, FloatExceptionHandler);

		/*
		 * Reset some signals that are accepted by postmaster but not by
		 * backend
		 */
		pqsignal(SIGCHLD, SIG_DFL); /* system() requires this on some
									 * platforms */
	}

	pqinitmask();

	if (IsUnderPostmaster)
	{
		/* We allow SIGQUIT (quickdie) at all times */
		sigdelset(&BlockSig, SIGQUIT);
	}

	PG_SETMASK(&BlockSig);		/* block everything except SIGQUIT */

	if (!IsUnderPostmaster)
	{
		/*
		 * Validate we have been given a reasonable-looking DataDir (if under
		 * postmaster, assume postmaster did this already).
		 */
		checkDataDir();

		/* Change into DataDir (if under postmaster, was done already) */
		ChangeToDataDir();

		/*
		 * Create lockfile for data directory.
		 */
		CreateDataDirLockFile(false);

		/* read control file (error checking and contains config ) */
		LocalProcessControlFile(false);

		/* Initialize MaxBackends (if under postmaster, was done already) */
		InitializeMaxBackends();
	}

	/* Early initialization */
	BaseInit();

	/*
	 * Create a per-backend PGPROC struct in shared memory, except in the
	 * EXEC_BACKEND case where this was done in SubPostmasterMain. We must do
	 * this before we can use LWLocks (and in the EXEC_BACKEND case we already
	 * had to do some stuff with LWLocks).
	 */
#ifdef EXEC_BACKEND
	if (!IsUnderPostmaster)
		InitProcess();
#else
	InitProcess();
#endif

	/* We need to allow SIGINT, etc during the initial transaction */
	PG_SETMASK(&UnBlockSig);

	/*
	 * General initialization.
	 *
	 * NOTE: if you are tempted to add code in this vicinity, consider putting
	 * it inside InitPostgres() instead.  In particular, anything that
	 * involves database access should be there, not here.
	 */
	InitPostgres(dbname, InvalidOid, username, InvalidOid, NULL, false);

	/*
	 * If the PostmasterContext is still around, recycle the space; we don't
	 * need it anymore after InitPostgres completes.  Note this does not trash
	 * *MyProcPort, because ConnCreate() allocated that space with malloc()
	 * ... else we'd need to copy the Port data first.  Also, subsidiary data
	 * such as the username isn't lost either; see ProcessStartupPacket().
	 */
	if (PostmasterContext)
	{
		MemoryContextDelete(PostmasterContext);
		PostmasterContext = NULL;
	}

	SetProcessingMode(NormalProcessing);

	/*
	 * Now all GUC states are fully set up.  Report them to client if
	 * appropriate.
	 */
	BeginReportingGUCOptions();

	/*
	 * Also set up handler to log session end; we have to wait till now to be
	 * sure Log_disconnections has its final value.
	 */
	if (IsUnderPostmaster && Log_disconnections)
		on_proc_exit(log_disconnections, 0);

	/* Perform initialization specific to a WAL sender process. */
	if (am_walsender)
		InitWalSender();

	/*
	 * process any libraries that should be preloaded at backend start (this
	 * likewise can't be done until GUC settings are complete)
	 */
	process_session_preload_libraries();

	/*
	 * Send this backend's cancellation info to the frontend.
	 */
	if (whereToSendOutput == DestRemote)
	{
		StringInfoData buf;

		pq_beginmessage(&buf, 'K');
		pq_sendint32(&buf, (int32) MyProcPid);
		pq_sendint32(&buf, (int32) MyCancelKey);
		pq_endmessage(&buf);
		/* Need not flush since ReadyForQuery will do it. */
	}

	/* Welcome banner for standalone case */
	if (whereToSendOutput == DestDebug)
		printf("\nPostgreSQL stand-alone backend %s\n", PG_VERSION);

	/*
	 * Create the memory context we will use in the main loop.
	 *
	 * MessageContext is reset once per iteration of the main loop, ie, upon
	 * completion of processing of each command message from the client.
	 */
	MessageContext = AllocSetContextCreate(TopMemoryContext,
										   "MessageContext",
										   ALLOCSET_DEFAULT_SIZES);

	/*
	 * Create memory context and buffer used for RowDescription messages. As
	 * SendRowDescriptionMessage(), via exec_describe_statement_message(), is
	 * frequently executed for ever single statement, we don't want to
	 * allocate a separate buffer every time.
	 */
	row_description_context = AllocSetContextCreate(TopMemoryContext,
													"RowDescriptionContext",
													ALLOCSET_DEFAULT_SIZES);
	MemoryContextSwitchTo(row_description_context);
	initStringInfo(&row_description_buf);
	MemoryContextSwitchTo(TopMemoryContext);

	/*
	 * Remember stand-alone backend startup time
	 */
	if (!IsUnderPostmaster)
		PgStartTime = GetCurrentTimestamp();

	/*
	 * POSTGRES main processing loop begins here
	 *
	 * If an exception is encountered, processing resumes here so we abort the
	 * current transaction and start a new one.
	 *
	 * You might wonder why this isn't coded as an infinite loop around a
	 * PG_TRY construct.  The reason is that this is the bottom of the
	 * exception stack, and so with PG_TRY there would be no exception handler
	 * in force at all during the CATCH part.  By leaving the outermost setjmp
	 * always active, we have at least some chance of recovering from an error
	 * during error recovery.  (If we get into an infinite loop thereby, it
	 * will soon be stopped by overflow of elog.c's internal state stack.)
	 *
	 * Note that we use sigsetjmp(..., 1), so that this function's signal mask
	 * (to wit, UnBlockSig) will be restored when longjmp'ing to here.  This
	 * is essential in case we longjmp'd out of a signal handler on a platform
	 * where that leaves the signal blocked.  It's not redundant with the
	 * unblock in AbortTransaction() because the latter is only called if we
	 * were inside a transaction.
	 */

	if (sigsetjmp(local_sigjmp_buf, 1) != 0)
	{
		/*
		 * NOTE: if you are tempted to add more code in this if-block,
		 * consider the high probability that it should be in
		 * AbortTransaction() instead.  The only stuff done directly here
		 * should be stuff that is guaranteed to apply *only* for outer-level
		 * error recovery, such as adjusting the FE/BE protocol status.
		 */

		/* Since not using PG_TRY, must reset error stack by hand */
		error_context_stack = NULL;

		/* Prevent interrupts while cleaning up */
		HOLD_INTERRUPTS();

		/*
		 * Forget any pending QueryCancel request, since we're returning to
		 * the idle loop anyway, and cancel any active timeout requests.  (In
		 * future we might want to allow some timeout requests to survive, but
		 * at minimum it'd be necessary to do reschedule_timeouts(), in case
		 * we got here because of a query cancel interrupting the SIGALRM
		 * interrupt handler.)	Note in particular that we must clear the
		 * statement and lock timeout indicators, to prevent any future plain
		 * query cancels from being misreported as timeouts in case we're
		 * forgetting a timeout cancel.
		 */
		disable_all_timeouts(false);
		QueryCancelPending = false; /* second to avoid race condition */
		stmt_timeout_active = false;

		/* Not reading from the client anymore. */
		DoingCommandRead = false;

		/* Make sure libpq is in a good state */
		pq_comm_reset();

		/* Report the error to the client and/or server log */
		EmitErrorReport();

		/*
		 * Make sure debug_query_string gets reset before we possibly clobber
		 * the storage it points at.
		 */
		debug_query_string = NULL;

		/*
		 * Abort the current transaction in order to recover.
		 */
		AbortCurrentTransaction();

		if (am_walsender)
			WalSndErrorCleanup();

		PortalErrorCleanup();
		SPICleanup();

		/*
		 * We can't release replication slots inside AbortTransaction() as we
		 * need to be able to start and abort transactions while having a slot
		 * acquired. But we never need to hold them across top level errors,
		 * so releasing here is fine. There's another cleanup in ProcKill()
		 * ensuring we'll correctly cleanup on FATAL errors as well.
		 */
		if (MyReplicationSlot != NULL)
			ReplicationSlotRelease();

		/* We also want to cleanup temporary slots on error. */
		ReplicationSlotCleanup();

		jit_reset_after_error();

		/*
		 * Now return to normal top-level context and clear ErrorContext for
		 * next time.
		 */
		MemoryContextSwitchTo(TopMemoryContext);
		FlushErrorState();

		/*
		 * If we were handling an extended-query-protocol message, initiate
		 * skip till next Sync.  This also causes us not to issue
		 * ReadyForQuery (until we get Sync).
		 */
		if (doing_extended_query_message)
			ignore_till_sync = true;

		/* We don't have a transaction command open anymore */
		xact_started = false;

		/*
		 * If an error occurred while we were reading a message from the
		 * client, we have potentially lost track of where the previous
		 * message ends and the next one begins.  Even though we have
		 * otherwise recovered from the error, we cannot safely read any more
		 * messages from the client, so there isn't much we can do with the
		 * connection anymore.
		 */
		if (pq_is_reading_msg())
			ereport(FATAL,
					(errcode(ERRCODE_PROTOCOL_VIOLATION),
					 errmsg("terminating connection because protocol synchronization was lost")));

		/* Now we can allow interrupts again */
		RESUME_INTERRUPTS();
	}

	/* We can now handle ereport(ERROR) */
	PG_exception_stack = &local_sigjmp_buf;

	if (!ignore_till_sync)
		send_ready_for_query = true;	/* initially, or after error */

	/*
	 * Non-error queries loop here.
	 */

	for (;;)
	{
		printf("loop (PostgresMain)\n");
		
		/*
		 * At top of loop, reset extended-query-message flag, so that any
		 * errors encountered in "idle" state don't provoke skip.
		 */
		doing_extended_query_message = false;

		/*
		 * Release storage left over from prior query cycle, and create a new
		 * query input buffer in the cleared MessageContext.
		 */
		MemoryContextSwitchTo(MessageContext);
		MemoryContextResetAndDeleteChildren(MessageContext);

		initStringInfo(&input_message);

		/*
		 * Also consider releasing our catalog snapshot if any, so that it's
		 * not preventing advance of global xmin while we wait for the client.
		 */
		InvalidateCatalogSnapshotConditionally();

		/*
		 * (1) If we've reached idle state, tell the frontend we're ready for
		 * a new query.
		 *
		 * Note: this includes fflush()'ing the last of the prior output.
		 *
		 * This is also a good time to send collected statistics to the
		 * collector, and to update the PS stats display.  We avoid doing
		 * those every time through the message loop because it'd slow down
		 * processing of batched messages, and because we don't want to report
		 * uncommitted updates (that confuses autovacuum).  The notification
		 * processor wants a call too, if we are not in a transaction block.
		 */
		if (send_ready_for_query)
		{
			if (IsAbortedTransactionBlockState())
			{
				set_ps_display("idle in transaction (aborted)", false);
				pgstat_report_activity(STATE_IDLEINTRANSACTION_ABORTED, NULL);

				/* Start the idle-in-transaction timer */
				if (IdleInTransactionSessionTimeout > 0)
				{
					disable_idle_in_transaction_timeout = true;
					enable_timeout_after(IDLE_IN_TRANSACTION_SESSION_TIMEOUT,
										 IdleInTransactionSessionTimeout);
				}
			}
			else if (IsTransactionOrTransactionBlock())
			{
				set_ps_display("idle in transaction", false);
				pgstat_report_activity(STATE_IDLEINTRANSACTION, NULL);

				/* Start the idle-in-transaction timer */
				if (IdleInTransactionSessionTimeout > 0)
				{
					disable_idle_in_transaction_timeout = true;
					enable_timeout_after(IDLE_IN_TRANSACTION_SESSION_TIMEOUT,
										 IdleInTransactionSessionTimeout);
				}
			}
			else
			{
				/* Send out notify signals and transmit self-notifies */
				ProcessCompletedNotifies();

				/*
				 * Also process incoming notifies, if any.  This is mostly to
				 * ensure stable behavior in tests: if any notifies were
				 * received during the just-finished transaction, they'll be
				 * seen by the client before ReadyForQuery is.
				 */
				if (notifyInterruptPending)
					ProcessNotifyInterrupt();

				pgstat_report_stat(false);

				set_ps_display("idle", false);
				pgstat_report_activity(STATE_IDLE, NULL);
			}

			ReadyForQuery(whereToSendOutput);
			send_ready_for_query = false;
		}

		/*
		 * (2) Allow asynchronous signals to be executed immediately if they
		 * come in while we are waiting for client input. (This must be
		 * conditional since we don't want, say, reads on behalf of COPY FROM
		 * STDIN doing the same thing.)
		 */
		DoingCommandRead = true;

		if (query_num_recorded){
			printf("Not query num checked\n");
		}
		query_num_recorded = false;		

		if (start_time_recorded){
			printf("Not time checked\n");
		}
		start_time_recorded = false;

		if (num_rows_recorded){
			printf("Not num rows checked\n");
		}
		num_rows_recorded = false;		

		/*
		 * (3) read a command (loop blocks here)
		 */
		firstchar = ReadCommand(&input_message);
		printf("------------------------------------------new loop------------------------------------------\n");

		if ((SIM_ADAPTIVE_RANGE) & (USE_ADAPTIVE_RANGE)){
			if (!inited){
				printf("arg case 1/1 - use adaptive range + initial values\n");
				
				get_init_values(&data_num1, &data_num2, &data_num3, &exec_time1, &exec_time2, &exec_time3, &data1_len, &data2_len, &data3_len);
				exec_coef1 = (double **)malloc(sizeof(double) * QUERYNUM);
				exec_coef2 = (double **)malloc(sizeof(double) * QUERYNUM);
				exec_coef3 = (double **)malloc(sizeof(double) * QUERYNUM);

				for (int i = 0 ; i < QUERYNUM ; i++){
					if (adjust_range(data_num1[i], data_num2[i], exec_time1[i], exec_time2[i], &data1_len[i], &data2_len[i],
									&data_num1[i], &data_num2[i], &exec_time1[i], &exec_time2[i], &exec_coef1[i], &exec_coef2[i], true)){
						printf("Error occured in adj 1\n");
					}
					if (adjust_range(data_num2[i], data_num3[i], exec_time2[i], exec_time3[i], &data2_len[i], &data3_len[i],
									&data_num2[i], &data_num3[i], &exec_time2[i], &exec_time3[i], &exec_coef2[i], &exec_coef3[i], false)){
						printf("Error occured in adj 2\n");
					}
				}

				inited = true;
				// printf("data1 len: %d data2 len: %d data3 len: %d\n", data1_len[query_num], data2_len[query_num], data3_len[query_num]);
			}
		} else if (USE_ADAPTIVE_RANGE){
			if (!inited){
				printf("arg case 0/1 - use adaptive range, but start from zero\n");
				int* data1_len = (int *)malloc(sizeof(int) * QUERYNUM);
				int* data2_len = (int *)malloc(sizeof(int) * QUERYNUM);
				int* data3_len = (int *)malloc(sizeof(int) * QUERYNUM);

				exec_coef1 = (double **)malloc(sizeof(double) * QUERYNUM);
				exec_coef2 = (double **)malloc(sizeof(double) * QUERYNUM);
				exec_coef3 = (double **)malloc(sizeof(double) * QUERYNUM);

				double** data_num1 = (double **)malloc(sizeof(double) * QUERYNUM);
				double** data_num2 = (double **)malloc(sizeof(double) * QUERYNUM);
				double** data_num3 = (double **)malloc(sizeof(double) * QUERYNUM);
				double** exec_time1 = (double **)malloc(sizeof(double) * QUERYNUM);
				double** exec_time2 = (double **)malloc(sizeof(double) * QUERYNUM);
				double** exec_time3 = (double **)malloc(sizeof(double) * QUERYNUM);

				for (int i = 0 ; i < QUERYNUM ; i++){
					data_num1[i] = (double *)malloc(sizeof(double) * DATASIZE);
					data_num2[i] = (double *)malloc(sizeof(double) * DATASIZE);
					data_num3[i] = (double *)malloc(sizeof(double) * DATASIZE);
					exec_time1[i] = (double *)malloc(sizeof(double) * DATASIZE);
					exec_time2[i] = (double *)malloc(sizeof(double) * DATASIZE);
					exec_time3[i] = (double *)malloc(sizeof(double) * DATASIZE);
				}

				inited = true;
			}
		} else if (SIM_ADAPTIVE_RANGE){
			if (!inited){
				printf("arg case 1/0 - simulate adaptive range once");
				get_init_values(&data_num1, &data_num2, &data_num3, &exec_time1, &exec_time2, &exec_time3, &data1_len, &data2_len, &data3_len);
				
				exec_coef1 = (double **)malloc(sizeof(double) * QUERYNUM);
				exec_coef2 = (double **)malloc(sizeof(double) * QUERYNUM);
				exec_coef3 = (double **)malloc(sizeof(double) * QUERYNUM);

				int query_num = Q1;
				
				printf("Init Restult\n");
				print_data(data_num1[query_num], data1_len[query_num]);
				printf("data1 len: %d\n", data1_len[query_num]);

				print_data(data_num2[query_num], data2_len[query_num]);
				printf("data2 len: %d\n", data2_len[query_num]);

				print_data(data_num3[query_num], data3_len[query_num]);
				printf("data3 len: %d\n", data3_len[query_num]);
				
				if (adjust_range(data_num1[query_num], data_num2[query_num], exec_time1[query_num], exec_time2[query_num], &data1_len[query_num], &data2_len[query_num],
								&data_num1[query_num], &data_num2[query_num], &exec_time1[query_num], &exec_time2[query_num], &exec_coef1[query_num], &exec_coef2[query_num], true)){
					printf("Error occured in adj 1\n");
				}
				if (adjust_range(data_num2[query_num], data_num3[query_num], exec_time2[query_num], exec_time3[query_num], &data2_len[query_num], &data3_len[query_num],
								&data_num2[query_num], &data_num3[query_num], &exec_time2[query_num], &exec_time3[query_num], &exec_coef2[query_num], &exec_coef3[query_num], false)){
					printf("Error occured in adj 2\n");
				}
				
				printf("Final Restult\n");
				print_data(data_num1[query_num], data1_len[query_num]);
				for (int x = 0 ; x < EXEC_ORDER + 1 ; x++){
					printf("%e ", exec_coef1[query_num][x]);
				}
				printf("\n");
				printf("data1 len: %d\n", data1_len[query_num]);

				print_data(data_num2[query_num], data2_len[query_num]);
				for (int y = 0 ; y < EXEC_ORDER + 1 ; y++){
					printf("%e ", exec_coef2[query_num][y]);
				}
				printf("\n");
				printf("data2 len: %d\n", data2_len[query_num]);

				print_data(data_num3[query_num], data3_len[query_num]);
				for (int z = 0 ; z < EXEC_ORDER + 1 ; z++){
					printf("%e ", exec_coef3[query_num][z]);
				}
				printf("\n");
				printf("data3 len: %d\n", data3_len[query_num]);
				
				double new_data_num_predict = 375000000;
				double new_exec_time_predict = 0;

				if (new_data_num_predict <= data_num2[query_num][0]){
					new_exec_time_predict = polyval(new_data_num_predict, exec_coef1[query_num]);
				} else if (new_data_num_predict <= data_num3[query_num][0]){
					new_exec_time_predict = polyval(new_data_num_predict, exec_coef2[query_num]);
				} else{
					new_exec_time_predict = polyval(new_data_num_predict, exec_coef3[query_num]);
				}

				printf("Predicted for %lf -> %lf\n", new_data_num_predict, new_exec_time_predict);

				double new_data_num_add = 35000 / 1000;
				double new_exec_time_add = 39.5;

				add_new_data(&data_num1[query_num], &data_num2[query_num],  &data_num3[query_num], 
							&exec_time1[query_num], &exec_time2[query_num], &exec_time3[query_num],
							&data1_len[query_num], &data2_len[query_num], &data3_len[query_num],
							&exec_coef1[query_num], &exec_coef2[query_num],  &exec_coef3[query_num],
							new_data_num_add, new_exec_time_add);

				printf("Final Restult 2\n");
				print_data(data_num1[query_num], data1_len[query_num]);
				for (int x = 0 ; x < EXEC_ORDER + 1 ; x++){
					printf("%e ", exec_coef1[query_num][x]);
				}
				printf("\n");
				printf("data1 len: %d\n", data1_len[query_num]);

				print_data(data_num2[query_num], data2_len[query_num]);
				for (int y = 0 ; y < EXEC_ORDER + 1 ; y++){
					printf("%e ", exec_coef2[query_num][y]);
				}
				printf("\n");
				printf("data2 len: %d\n", data2_len[query_num]);

				print_data(data_num3[query_num], data3_len[query_num]);
				for (int z = 0 ; z < EXEC_ORDER + 1 ; z++){
					printf("%e ", exec_coef3[query_num][z]);
				}
				printf("\n");
				printf("data3 len: %d\n", data3_len[query_num]);

				inited = true;
			}
		} else{
			if (!inited){
				printf("arg case 0/0 - not use adaptive range");
			}
			inited = true;
		}

		start_time_recorded = true;
		query_start_time = clock();
		printf("start time: %lf\n", (double)query_start_time);

		/*
		 * (4) turn off the idle-in-transaction timeout, if active.  We do
		 * this before step (5) so that any last-moment timeout is certain to
		 * be detected in step (5).
		 */
		if (disable_idle_in_transaction_timeout)
		{
			disable_timeout(IDLE_IN_TRANSACTION_SESSION_TIMEOUT, false);
			disable_idle_in_transaction_timeout = false;
		}

		/*
		 * (5) disable async signal conditions again.
		 *
		 * Query cancel is supposed to be a no-op when there is no query in
		 * progress, so if a query cancel arrived while we were idle, just
		 * reset QueryCancelPending. ProcessInterrupts() has that effect when
		 * it's called when DoingCommandRead is set, so check for interrupts
		 * before resetting DoingCommandRead.
		 */
		CHECK_FOR_INTERRUPTS();
		DoingCommandRead = false;

		/*
		 * (6) check for any other interesting events that happened while we
		 * slept.
		 */
		if (ConfigReloadPending)
		{
			ConfigReloadPending = false;
			ProcessConfigFile(PGC_SIGHUP);
		}

		/*
		 * (7) process the command.  But ignore it if we're skipping till
		 * Sync.
		 */
		if (ignore_till_sync && firstchar != EOF)
			continue;

		switch (firstchar)
		{
			case 'Q':			/* simple query */
				{
					const char *query_string;

					/* Set statement_timestamp() */
					SetCurrentStatementStartTimestamp();

					query_string = pq_getmsgstring(&input_message);
					pq_getmsgend(&input_message);

					printf("exec_simple_query (PostgresMain)\n");
					printf("query: %s\n", query_string);

					if (am_walsender)
					{
						if (!exec_replication_command(query_string))
							exec_simple_query(query_string);
					}
					else
						exec_simple_query(query_string);

					if (start_time_recorded){
						query_end_time = clock();
					}

					if (train_flag){
						printf("train flag come----\n");
						//char* train_table_create_query = tree_table_query_creator();
						//printf("query: %s\n", train_table_create_query);
						//exec_simple_query(train_table_create_query);
						//train_flag = false;
						//printf("train flag solved----\n");
						//free(train_table_create_query);
					}


					if ((SIM_ADAPTIVE_RANGE) & (USE_ADAPTIVE_RANGE)){
						if ((cpu_used) & (query_num_recorded & start_time_recorded & num_rows_recorded)){
							double new_exec_time_add = ((double)(query_end_time - query_start_time) / CLOCKS_PER_SEC) * 1000;
							printf("arg case 1/1 - new data come (query num: %d / data num: %f / execute time: %f)\n", query_num + 1, num_rows, new_exec_time_add);

							double new_data_num_add = num_rows / 1000;
							add_new_data(&data_num1[query_num], &data_num2[query_num], &data_num3[query_num], 
										&exec_time1[query_num], &exec_time2[query_num], &exec_time3[query_num],
										&data1_len[query_num], &data2_len[query_num], &data3_len[query_num],
										&exec_coef1[query_num], &exec_coef2[query_num], &exec_coef3[query_num],
										new_data_num_add, new_exec_time_add);
									
							//printf("arg case 1/1 - data1 len: %d data2 len: %d data3 len: %d\n", data1_len[query_num], data2_len[query_num], data3_len[query_num]);
							printf("arg case 1/1 - data successfully added to data range\n");
						}
						
					} else if (USE_ADAPTIVE_RANGE){
						if ((cpu_used) & (query_num_recorded & start_time_recorded & num_rows_recorded)){
							double new_exec_time_add = ((double)(query_end_time - query_start_time) / CLOCKS_PER_SEC) * 1000;
							printf("arg case 0/1 - new data come (query num: %d / data num: %f / execute time: %f)\n", query_num + 1, num_rows, new_exec_time_add);

							double new_data_num_add = num_rows / 1000;
							add_new_data(&data_num1[query_num], &data_num2[query_num], &data_num3[query_num], 
										&exec_time1[query_num], &exec_time2[query_num], &exec_time3[query_num],
										&data1_len[query_num], &data2_len[query_num], &data3_len[query_num],
										&exec_coef1[query_num], &exec_coef2[query_num], &exec_coef3[query_num],
										new_data_num_add, new_exec_time_add);
							//printf("arg case 0/1 - data1 len: %d data2 len: %d data3 len: %d\n", data1_len[query_num], data2_len[query_num], data3_len[query_num]);
							printf("arg case 0/1 - data successfully added to data range\n");
						}

					} 
					// printf("End of loop - Query num: %d [data1 len: %d, data2 len: %d, data3 len: %d]\n", query_num + 1, data1_len[query_num], data2_len[query_num], data3_len[query_num]);

					query_num_recorded = false;
					start_time_recorded = false;
					num_rows_recorded = false;

					send_ready_for_query = true;
				}
				break;

			case 'P':			/* parse */
				{
					const char *stmt_name;
					const char *query_string;
					int			numParams;
					Oid		   *paramTypes = NULL;

					forbidden_in_wal_sender(firstchar);

					/* Set statement_timestamp() */
					SetCurrentStatementStartTimestamp();

					stmt_name = pq_getmsgstring(&input_message);
					query_string = pq_getmsgstring(&input_message);
					numParams = pq_getmsgint(&input_message, 2);
					if (numParams > 0)
					{
						paramTypes = (Oid *) palloc(numParams * sizeof(Oid));
						for (int i = 0; i < numParams; i++)
							paramTypes[i] = pq_getmsgint(&input_message, 4);
					}
					pq_getmsgend(&input_message);

					exec_parse_message(query_string, stmt_name,
									   paramTypes, numParams);
				}
				break;

			case 'B':			/* bind */
				forbidden_in_wal_sender(firstchar);

				/* Set statement_timestamp() */
				SetCurrentStatementStartTimestamp();

				/*
				 * this message is complex enough that it seems best to put
				 * the field extraction out-of-line
				 */
				exec_bind_message(&input_message);
				break;

			case 'E':			/* execute */
				{
					const char *portal_name;
					int			max_rows;

					forbidden_in_wal_sender(firstchar);

					/* Set statement_timestamp() */
					SetCurrentStatementStartTimestamp();

					portal_name = pq_getmsgstring(&input_message);
					max_rows = pq_getmsgint(&input_message, 4);
					pq_getmsgend(&input_message);

					exec_execute_message(portal_name, max_rows);
				}
				break;

			case 'F':			/* fastpath function call */
				forbidden_in_wal_sender(firstchar);

				/* Set statement_timestamp() */
				SetCurrentStatementStartTimestamp();

				/* Report query to various monitoring facilities. */
				pgstat_report_activity(STATE_FASTPATH, NULL);
				set_ps_display("<FASTPATH>", false);

				/* start an xact for this function invocation */
				start_xact_command();

				/*
				 * Note: we may at this point be inside an aborted
				 * transaction.  We can't throw error for that until we've
				 * finished reading the function-call message, so
				 * HandleFunctionRequest() must check for it after doing so.
				 * Be careful not to do anything that assumes we're inside a
				 * valid transaction here.
				 */

				/* switch back to message context */
				MemoryContextSwitchTo(MessageContext);

				HandleFunctionRequest(&input_message);

				/* commit the function-invocation transaction */
				finish_xact_command();

				send_ready_for_query = true;
				break;

			case 'C':			/* close */
				{
					int			close_type;
					const char *close_target;

					forbidden_in_wal_sender(firstchar);

					close_type = pq_getmsgbyte(&input_message);
					close_target = pq_getmsgstring(&input_message);
					pq_getmsgend(&input_message);

					switch (close_type)
					{
						case 'S':
							if (close_target[0] != '\0')
								DropPreparedStatement(close_target, false);
							else
							{
								/* special-case the unnamed statement */
								drop_unnamed_stmt();
							}
							break;
						case 'P':
							{
								Portal		portal;

								portal = GetPortalByName(close_target);
								if (PortalIsValid(portal))
									PortalDrop(portal, false);
							}
							break;
						default:
							ereport(ERROR,
									(errcode(ERRCODE_PROTOCOL_VIOLATION),
									 errmsg("invalid CLOSE message subtype %d",
											close_type)));
							break;
					}

					if (whereToSendOutput == DestRemote)
						pq_putemptymessage('3');	/* CloseComplete */
				}
				break;

			case 'D':			/* describe */
				{
					int			describe_type;
					const char *describe_target;

					forbidden_in_wal_sender(firstchar);

					/* Set statement_timestamp() (needed for xact) */
					SetCurrentStatementStartTimestamp();

					describe_type = pq_getmsgbyte(&input_message);
					describe_target = pq_getmsgstring(&input_message);
					pq_getmsgend(&input_message);

					switch (describe_type)
					{
						case 'S':
							exec_describe_statement_message(describe_target);
							break;
						case 'P':
							exec_describe_portal_message(describe_target);
							break;
						default:
							ereport(ERROR,
									(errcode(ERRCODE_PROTOCOL_VIOLATION),
									 errmsg("invalid DESCRIBE message subtype %d",
											describe_type)));
							break;
					}
				}
				break;

			case 'H':			/* flush */
				pq_getmsgend(&input_message);
				if (whereToSendOutput == DestRemote)
					pq_flush();
				break;

			case 'S':			/* sync */
				pq_getmsgend(&input_message);
				finish_xact_command();
				send_ready_for_query = true;
				break;

				/*
				 * 'X' means that the frontend is closing down the socket. EOF
				 * means unexpected loss of frontend connection. Either way,
				 * perform normal shutdown.
				 */
			case 'X':
			case EOF:

				/*
				 * Reset whereToSendOutput to prevent ereport from attempting
				 * to send any more messages to client.
				 */
				if (whereToSendOutput == DestRemote)
					whereToSendOutput = DestNone;

				/*
				 * NOTE: if you are tempted to add more code here, DON'T!
				 * Whatever you had in mind to do should be set up as an
				 * on_proc_exit or on_shmem_exit callback, instead. Otherwise
				 * it will fail to be called during other backend-shutdown
				 * scenarios.
				 */
				proc_exit(0);

			case 'd':			/* copy data */
			case 'c':			/* copy done */
			case 'f':			/* copy fail */

				/*
				 * Accept but ignore these messages, per protocol spec; we
				 * probably got here because a COPY failed, and the frontend
				 * is still sending data.
				 */
				break;

			default:
				ereport(FATAL,
						(errcode(ERRCODE_PROTOCOL_VIOLATION),
						 errmsg("invalid frontend message type %d",
								firstchar)));
		}
	}							/* end of input-reading loop */
}

/*
 * Throw an error if we're a WAL sender process.
 *
 * This is used to forbid anything else than simple query protocol messages
 * in a WAL sender process.  'firstchar' specifies what kind of a forbidden
 * message was received, and is used to construct the error message.
 */
static void
forbidden_in_wal_sender(char firstchar)
{
	if (am_walsender)
	{
		if (firstchar == 'F')
			ereport(ERROR,
					(errcode(ERRCODE_PROTOCOL_VIOLATION),
					 errmsg("fastpath function calls not supported in a replication connection")));
		else
			ereport(ERROR,
					(errcode(ERRCODE_PROTOCOL_VIOLATION),
					 errmsg("extended query protocol not supported in a replication connection")));
	}
}


/*
 * Obtain platform stack depth limit (in bytes)
 *
 * Return -1 if unknown
 */
long
get_stack_depth_rlimit(void)
{
#if defined(HAVE_GETRLIMIT) && defined(RLIMIT_STACK)
	static long val = 0;

	/* This won't change after process launch, so check just once */
	if (val == 0)
	{
		struct rlimit rlim;

		if (getrlimit(RLIMIT_STACK, &rlim) < 0)
			val = -1;
		else if (rlim.rlim_cur == RLIM_INFINITY)
			val = LONG_MAX;
		/* rlim_cur is probably of an unsigned type, so check for overflow */
		else if (rlim.rlim_cur >= LONG_MAX)
			val = LONG_MAX;
		else
			val = rlim.rlim_cur;
	}
	return val;
#else							/* no getrlimit */
#if defined(WIN32) || defined(__CYGWIN__)
	/* On Windows we set the backend stack size in src/backend/Makefile */
	return WIN32_STACK_RLIMIT;
#else							/* not windows ... give up */
	return -1;
#endif
#endif
}


static struct rusage Save_r;
static struct timeval Save_t;

void
ResetUsage(void)
{
	getrusage(RUSAGE_SELF, &Save_r);
	gettimeofday(&Save_t, NULL);
}

void
ShowUsage(const char *title)
{
	StringInfoData str;
	struct timeval user,
				sys;
	struct timeval elapse_t;
	struct rusage r;

	getrusage(RUSAGE_SELF, &r);
	gettimeofday(&elapse_t, NULL);
	memcpy((char *) &user, (char *) &r.ru_utime, sizeof(user));
	memcpy((char *) &sys, (char *) &r.ru_stime, sizeof(sys));
	if (elapse_t.tv_usec < Save_t.tv_usec)
	{
		elapse_t.tv_sec--;
		elapse_t.tv_usec += 1000000;
	}
	if (r.ru_utime.tv_usec < Save_r.ru_utime.tv_usec)
	{
		r.ru_utime.tv_sec--;
		r.ru_utime.tv_usec += 1000000;
	}
	if (r.ru_stime.tv_usec < Save_r.ru_stime.tv_usec)
	{
		r.ru_stime.tv_sec--;
		r.ru_stime.tv_usec += 1000000;
	}

	/*
	 * The only stats we don't show here are ixrss, idrss, isrss.  It takes
	 * some work to interpret them, and most platforms don't fill them in.
	 */
	initStringInfo(&str);

	appendStringInfoString(&str, "! system usage stats:\n");
	appendStringInfo(&str,
					 "!\t%ld.%06ld s user, %ld.%06ld s system, %ld.%06ld s elapsed\n",
					 (long) (r.ru_utime.tv_sec - Save_r.ru_utime.tv_sec),
					 (long) (r.ru_utime.tv_usec - Save_r.ru_utime.tv_usec),
					 (long) (r.ru_stime.tv_sec - Save_r.ru_stime.tv_sec),
					 (long) (r.ru_stime.tv_usec - Save_r.ru_stime.tv_usec),
					 (long) (elapse_t.tv_sec - Save_t.tv_sec),
					 (long) (elapse_t.tv_usec - Save_t.tv_usec));
	appendStringInfo(&str,
					 "!\t[%ld.%06ld s user, %ld.%06ld s system total]\n",
					 (long) user.tv_sec,
					 (long) user.tv_usec,
					 (long) sys.tv_sec,
					 (long) sys.tv_usec);
#if defined(HAVE_GETRUSAGE)
	appendStringInfo(&str,
					 "!\t%ld kB max resident size\n",
#if defined(__darwin__)
	/* in bytes on macOS */
					 r.ru_maxrss / 1024
#else
	/* in kilobytes on most other platforms */
					 r.ru_maxrss
#endif
		);
	appendStringInfo(&str,
					 "!\t%ld/%ld [%ld/%ld] filesystem blocks in/out\n",
					 r.ru_inblock - Save_r.ru_inblock,
	/* they only drink coffee at dec */
					 r.ru_oublock - Save_r.ru_oublock,
					 r.ru_inblock, r.ru_oublock);
	appendStringInfo(&str,
					 "!\t%ld/%ld [%ld/%ld] page faults/reclaims, %ld [%ld] swaps\n",
					 r.ru_majflt - Save_r.ru_majflt,
					 r.ru_minflt - Save_r.ru_minflt,
					 r.ru_majflt, r.ru_minflt,
					 r.ru_nswap - Save_r.ru_nswap,
					 r.ru_nswap);
	appendStringInfo(&str,
					 "!\t%ld [%ld] signals rcvd, %ld/%ld [%ld/%ld] messages rcvd/sent\n",
					 r.ru_nsignals - Save_r.ru_nsignals,
					 r.ru_nsignals,
					 r.ru_msgrcv - Save_r.ru_msgrcv,
					 r.ru_msgsnd - Save_r.ru_msgsnd,
					 r.ru_msgrcv, r.ru_msgsnd);
	appendStringInfo(&str,
					 "!\t%ld/%ld [%ld/%ld] voluntary/involuntary context switches\n",
					 r.ru_nvcsw - Save_r.ru_nvcsw,
					 r.ru_nivcsw - Save_r.ru_nivcsw,
					 r.ru_nvcsw, r.ru_nivcsw);
#endif							/* HAVE_GETRUSAGE */

	/* remove trailing newline */
	if (str.data[str.len - 1] == '\n')
		str.data[--str.len] = '\0';

	ereport(LOG,
			(errmsg_internal("%s", title),
			 errdetail_internal("%s", str.data)));

	pfree(str.data);
}

/*
 * on_proc_exit handler to log end of session
 */
static void
log_disconnections(int code, Datum arg)
{
	Port	   *port = MyProcPort;
	long		secs;
	int			usecs;
	int			msecs;
	int			hours,
				minutes,
				seconds;

	TimestampDifference(MyStartTimestamp,
						GetCurrentTimestamp(),
						&secs, &usecs);
	msecs = usecs / 1000;

	hours = secs / SECS_PER_HOUR;
	secs %= SECS_PER_HOUR;
	minutes = secs / SECS_PER_MINUTE;
	seconds = secs % SECS_PER_MINUTE;

	ereport(LOG,
			(errmsg("disconnection: session time: %d:%02d:%02d.%03d "
					"user=%s database=%s host=%s%s%s",
					hours, minutes, seconds, msecs,
					port->user_name, port->database_name, port->remote_host,
					port->remote_port[0] ? " port=" : "", port->remote_port)));
}

/*
 * Start statement timeout timer, if enabled.
 *
 * If there's already a timeout running, don't restart the timer.  That
 * enables compromises between accuracy of timeouts and cost of starting a
 * timeout.
 */
static void
enable_statement_timeout(void)
{
	/* must be within an xact */
	Assert(xact_started);

	if (StatementTimeout > 0)
	{
		if (!stmt_timeout_active)
		{
			enable_timeout_after(STATEMENT_TIMEOUT, StatementTimeout);
			stmt_timeout_active = true;
		}
	}
	else
		disable_timeout(STATEMENT_TIMEOUT, false);
}

/*
 * Disable statement timeout, if active.
 */
static void
disable_statement_timeout(void)
{
	if (stmt_timeout_active)
	{
		disable_timeout(STATEMENT_TIMEOUT, false);

		stmt_timeout_active = false;
	}
}
