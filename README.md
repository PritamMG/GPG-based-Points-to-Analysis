Points-to Analysis using Generalized Points-to Graphs
======================================================
This repository provides an implementation of points-to analysis using the Generalized Points-to Graphs (GPG). A GPG is a graph with GPBs (Generalized Points-to Blocks) as nodes which in turn are sets of GPUs (Generalized Points-to Updates) that represent statements accessing pointers.

The GPG-based points-to analysis is implemented in GCC 4.7.2. It is tested on Ubuntu 14.04. This implementation is provided as a dynamic plugin for gcc 4.7.2.

We have provided an installation of gcc 4.7.2 and there is no need to build it from the source code. This has been done because building gcc-4.7.2 using contemporary version of gcc runs into many problems. Please download this file and copy it in the current direcoty. The complete set of steps needed to run the implementation are

    $cd GPG-based-Points-to-Analysis    # The top level directory.
    $tar xvfz gcc472.tgz                # This creates the subdirectory gcc472 containing the gcc installation.
    $cd gpg-imp                         # This contains the source of the GPG-based points-to analysis.
    $source set-lib-paths.sh            # `source` command instantiates the shell variables in the current shell.
    $make run                           # Builds the plugin and runs it on $(TEST) in the Makefile.
    
This produces the output of the analysis in file`result.233i.gpg`. Please refer to the file HOW_TO_READ_DATA for interpreting the data dumped by the implementation.

The impelmentation supports multiple variants of points-to analysis. They can be enabled by setting appropriate flags (present in the file `gpg-imp/GPU.h`)

1. For flow- and context-insensitive (FICI) analysis, set `FI_ANALYSIS` and `CI_ANALYSIS` to 1.
2. For flow-sensitive and context-insensitive (FICS) analysis, set `FI_ANALYSIS` to 0 and `CI_ANALYSIS` to 1.
3. For flow- and context-sensitive (FSCS) analysis (default option), set `FI_ANALYSIS` and `CI_ANALYSIS` to 0.

Additional flags such as `PRINT_DATA`, `DATA_MEAS` and `TIME_MEAS` are used to print GPGs at every program point (for every GPB constructed), data measurements, and time measurements respectively

The flag `BLOCKING` is set to 1 (by default) for GPG-based points-to analysis for points-to analysis.


Function `printGPG()` for a procedure prints the GPGs of the procedure. It lists the Entry and End GPBs of the GPG and summarizes the GPG with number of GPBs, number of unresolved recursive and indirect calls, number of GPUs and number of control flow edges.
It then prints every GPB, with the number of predecessors/successors (listing all predecessors/successors GPBs) and the GPUs contained in the GPBs. It finally prints the Flow-insensitive GPUs which includes the GPUs involving SSA variables and Array variables.

Note that SSA variables are resolved while constructing the Initial GPG by using def-use chains (i.e., SSA edges). Hence, no GPBs will have GPUs involving SSA variables.

PS: Options like `HEURISTICS` and `PAR_FI` are no longer used.
