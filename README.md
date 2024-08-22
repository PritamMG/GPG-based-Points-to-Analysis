Points-to Analysis using Generalized Points-to Graphs
======================================================
This repository provides an implementation of points-to analysis using the Generalized Points-to Graphs (GPG). A GPG is a graph with GPBs (Generalized Points-to Blocks) as nodes which in turn are sets of GPUs (Generalized Points-to Updates) that represent statements accessing pointers. A link to the copy of the paper will be made available soon after it is published. An [electronic appendix of the paper is available here](appendix-gpg-pta-v4.pdf). If you have any questions, please use the issues tab to raise it.

The GPG-based points-to analysis is implemented in gcc 4.7.2 as a dynamic plugin. We have also provided an installation of gcc 4.7.2 for x86_64 processors and there is no need to build it from the source code. This has been done because building gcc-4.7.2 using contemporary versions of gcc runs into many problems. 


Running the GPG-based Points-to Analysis
----------------------------------------
Please [download file gcc472.tgz file](https://drive.google.com/file/d/16ohWj5w-Ujks-qsqseGs3mUbtO3x05gX/view?usp=sharing) and copy it in the top level directory `GPG-based-Points-to-Analysis`. The souce of the plugin for GPG-based points-to analysis is contained in a sub-directory called `gpg-imp`. This sub-directory is contained in the top level directory `GPG-based-Points-to-Analysis`. The complete sequence of steps needed to run the implementation for the first time is as follows. For subsequent runs, a suitable combination of last three steps would suffice.

    $git clone https://github.com/PritamMG/GPG-based-Points-to-Analysis.git  # Get a copy of this repository
    $cd GPG-based-Points-to-Analysis    # The top level directory.
    $tar xvfz gcc472.tgz                # This creates the subdirectory gcc472 containing the gcc installation.
    $cd gpg-imp                         # This contains the source of the GPG-based points-to analysis.
    $source set-lib-paths.sh            # `source` command instantiates the shell variables in the current shell.
    $make run                           # Builds the plugin and runs it on $(TEST) in the Makefile.
    

This produces the output of the analysis in file`result.233i.gpg`. Please refer to the file [`HOW_TO_READ_GPG_DUMP`](HOW_TO_READ_GPG_DUMP.md) for interpreting the data dumped by the implementation.

The above steps have been tested on Ubuntu Ubuntu 14.04, Ubuntu 16.04, and Ubuntu 18.04, all running on x86_64. In some cases, the machines didn't have `g++-multilib` installed and hence the compilation did not work. Installing `g++-multilib` solved the problem.

Some Options Available for Running the Implementation
------------------------------------------------------

The implementation supports multiple variants of points-to analysis. They can be enabled by setting appropriate flags (present in the file `gpg-imp/GPU.h`)

1. For flow- and context-insensitive (FICI) analysis, set `FI_ANALYSIS` and `CI_ANALYSIS` to 1.
2. For flow-sensitive and context-insensitive (FICS) analysis, set `FI_ANALYSIS` to 0 and `CI_ANALYSIS` to 1.
3. For flow- and context-sensitive (FSCS) analysis (default option), set `FI_ANALYSIS` and `CI_ANALYSIS` to 0.

Additional flags such as `PRINT_DATA`, `DATA_MEAS` and `TIME_MEAS` are used to print GPGs at every program point (for every GPB constructed), data measurements, and time measurements respectively

The flag `BLOCKING` is set to 1 (by default) for GPG-based points-to analysis for points-to analysis. Options `HEURISTICS` and `PAR_FI` are no longer used.

**Error Resolution: Dynamic Linking Issue in ‘make run’ Command**

During execution of the 'make run' command in the sequence of steps needed to run the implementation, the build process may fail with an error message indicating that one or more (.h) header files are missing.
Since gcc 4.7.2 is implemented as a dynamic plugin, we need to dynamically link the header files to correct source **once**. 

To resolve the issue of missing header files, we need to take the following steps:
    1. **Identify the Missing Header File:**
        a. Check the error message to identify the missing header file. For example, example.h.
    2. **Locate the Header File:**
        a. Search your system or project directories to locate the missing header file using the find or locate command:
            i. find / -name example.h
            ii. locate example.h
        There could be ambiguity while executing this command, as there could be multiple header files with same name. Figuring            out the correct location of required header file should be done through carefully examining the error message. 
    3. Create a symbolic link:
        a. Use the ln command to create a symbolic link in a directory that is in the system's library search path:
            i. sudo ln -s /path/to/libexample.so /usr/lib/libexample.so
            ii. Replace /path/to/libexample.so with the actual path to the library found in step 2.
**Execute the make run command to check if the error is resolved.**
This sequence of steps could be required multiple times for successfully executing the 'make run' command. Once a dynamic link for every misplaced header file is created, the command should execute successfully. 
