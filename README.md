# Trinity: In-Database Near-Data Machine Learning Acceleration Platform for Advanced Data Analytics
---
## Abstract

The ability to perform machine learning (ML) tasks in a database management system (DBMS) is a new paradigm for conventional database systems as it enables advanced data analytics on top of well-established capabilities of DBMSs. However, the integration of ML in DBMSs introduces challenges in traditional CPU-based systems because of its higher computational demands and bigger data bandwidth requirements. To address this, hardware acceleration has become even more important in database systems, and the computational storage device (CSD) placing an accelerator near storage is considered as an effective solution due to its high processing power with no extra data movement cost. <br> <br> In this paper, we propose Trinity, an end-to-end database system that enables in-database, in-storage platform that accelerates advanced analytics queries invoking trained ML models along with complex data operations. By designing a full stack from DBMS's internal software components to hardware accelerator, Trinity enables in-database ML pipelines on the CSD. On the software side, we extend the internals of conventional DBMSs to utilize the accelerator in the SmartSSD. By integrating our performance cost model within the DBMS, analytics queries can be selectively offloaded to the accelerator in the SmartSSD to run the queries with optimal hardware backends. On the hardware side, we introduce a custom hardware accelerator design for FPGA that can directly unpack the data pages from a storage device and perform data and ML operations with parallel/pipelined computing units. Our evaluation shows that Trinity improves the end-to-end performance of analytics queries by 15.21x on average and up to 57.18x compared to the conventional CPU-based DBMS platform. We also show that the Trinity's performance can linearly scale up with multiple SmartSSDs, achieving nearly up to 200x speedup over the baseline with four SmartSSDs.

---
## Postgres+
### This directory contains the Trinity's software stack, Postgres+
- PostgreSQL+ is hardware-aware software stack for Trinity system based on open source Postgres. 
- PostgreSQL+ modifies the PostgreSQL’s internal subsystems such as query analyzer, optimizer, and executor to enable the use of SmartSSD backend within the DBMS.
- Postgres always uses the CPU to process queries, but Postgres+ uses a cost model to decide whether to process queries through CPU or offload to SmartSSD hardware. 
- Postgres+ can run the SmartSSD executor along with the CPU executor if necessary.  

### SmartSSD Cost Model
- Postgres+ uses the SmartSSD cost model to approximate the time consumption when it offloads work to a SmartSSD. 
- The total execution time of the SmartSSD can be expressed as sum of the host operation time, data transfer time, and FPGA kernel time. 
- By estimating these factors, the cost of hardware offloading can be calculated.

### CPU Cost Model
- Unlike the SmartSSD’s performance cost model, the CPU cost model is difficult to represent with a few linear equations as it is a complex system with influences such as caching and IO operations. 
- In addition, the query processing time in CPU shows different characteristics according to the complexity of the query. 
- Therefore, CPU cost model is triaged into a few groups based on the complexity and use a polynomial regression ML model in each group. 
- Also, to handle the problems that cost model may not work well on other systems, online fine-tuning method that adjusts the cost ranges to minimize the total amount of errors between the polynomial models and the measurements has been applied.
---
## License

This directory contains the source code distribution of the PostgreSQL database management system.

PostgreSQL is an advanced object-relational database management system that supports an extended subset of the SQL standard, including transactions, foreign keys, subqueries, triggers, user-defined types and functions. 
This distribution also contains C language bindings.

PostgreSQL has many language interfaces, many of which are listed here: <br>
	https://www.postgresql.org/download

See the file INSTALL for instructions on how to build and install PostgreSQL.  
That file also lists supported operating systems and hardware platforms and contains information regarding any other software packages that are required to build or run the PostgreSQL system.  

Copyright and license information can be found in the file COPYRIGHT.  
A comprehensive documentation set is included in this distribution; it can be read as described in the installation instructions.

The latest version of this software may be obtained at <br>
	  https://www.postgresql.org/download/.  

For more information look at our web site located at <br>
	  https://www.postgresql.org/.