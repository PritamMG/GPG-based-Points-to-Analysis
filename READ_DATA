Multiple variants of points-to analysis is implemented. They can be enabled by setting appropriate flags (present in gpg-imp/GPU.h)

1. Flow- and context-insensitive (FICI) analysis: Set FI_ANALYSIS and CI_ANALYSIS to 1. 
2. Flow-sensitive and context-insensitive (FICS) analysis: Set FI_ANALYSIS to 0 and CI_ANALYSIS to 1. 
2. Flow- and context-sensitive (FSCS) analysis (default option): Set FI_ANALYSIS and CI_ANALYSIS to 0. 

Additional flags such as PRINT_DATA, DATA_MEAS and TIME_MEAS are used to print GPGs at every program point (for every GPB constructed), data and time measurements. 

The flag BLOCKING is set to 1 (by default) for GPG-based points-to analysis for points-to analysis. 

The output of the analysis is dumped in the file result.233i.gpg.

printGPG() for a procedure prints the GPGs the procedure. It specifies the Entry and End GPB. It summarizes the GPG with number of GPBs, number of unresolved recursive and indirect calls, number of GPUs, number of control flow edges.
It then prints every GPB, with the number of predecessors/successors (lists all predecessors/successors) and the GPUs contained in the GPBs. It finally prints the Flow-insensitive GPUs which includes the SSA variables, Array variables.

Note that SSA variables are resolved while constructing the Initial GPG by using def-use chains. Hence, no GPBs will have GPUs involving SSA variables.

PS: Options like HEURISTICS and PAR_FI are no longer used.

The flag DATA_MEAS prints the following information:

1. Call Graph
	a. Number of nodes in the call graph (number of procedures)
	b. Number of edges in the call graph (caller-callee relationship)
	c. Number of monomorphic indirect calls (single callee for a call through a function pointer)
	d. Number of polymorphic indirect calls (multiple callees for a call through a function pointer)

2. Mod/Ref Analysis
	a. Number of pointers modified in each procedure (includes the indirect effect through callees)
	b. Number of pointers referenced in each procedure (includes the indirect effect through callees)
	c. Number of calls where at least one pointer is modified in its callee(s) 
	c. Number of calls where at least one pointer is referenced in its callee(s) 

3. Points-to Information
	a. Number of GPUs (points-to information) for every statement in the IR of GCC
		- Currently only the number of GPUs are printed. You can access the points-to information in the data structure PTS_INFO which gives
		  precise flow- and context-sensitive points-to information for all the pointers in the source code (this excludes the SSA variables). 		  

Additionally, a summary (in terms of number of GPBs, GPUs, control flow edges) is printed for every procedure.	
