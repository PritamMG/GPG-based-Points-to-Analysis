More Details About the Implementation
=====================================

Function `printGPG()` for the object representing a procedure prints the GPG the procedure. It specifies the Entry and End GPB. It summarizes the GPG with number of GPBs, number of unresolved recursive and indirect calls, number of GPUs, number of control flow edges. It then prints every GPB, with the number of predecessors/successors (lists all predecessors/successors) and the GPUs contained in the GPBs. It finally prints the Flow-insensitive GPUs which includes the SSA variables, Array variables.

Note that SSA variables are resolved while constructing the Initial GPG by using def-use chains. Hence, no GPBs will have GPUs involving SSA variables.

The flag `DATA_MEAS` prints the following information:

1. Call Graph
  * Number of nodes in the call graph (number of procedures)
  * Number of edges in the call graph (caller-callee relationship)
  * Number of monomorphic indirect calls (single callee for a call through a function pointer)
  * Number of polymorphic indirect calls (multiple callees for a call through a function pointer)

2. Mod/Ref Analysis
  * Number of pointers modified in each procedure (includes the indirect effect through callees)
  * Number of pointers referenced in each procedure (includes the indirect effect through callees)
  * Number of calls where at least one pointer is modified in its callee(s) 
  * Number of calls where at least one pointer is referenced in its callee(s) 

3. Points-to Information
  * Number of GPUs (points-to information) for every statement in the IR of GCC
     + Currently only the number of GPUs are printed. You can access the points-to information in the data structure `PTS_INFO` which gives precise flow- and context-sensitive points-to information for all the pointers in the source code (this excludes the SSA variables). 		  

Additionally, a summary (in terms of number of GPBs, GPUs, control flow edges) is printed for every procedure.	
