The detailed explanation is provided in PDF in following repository:

https://github.com/StarikTenger/Internship2025-report


# Timing anomaly searching framework

Provides a set of tools to research timing anomalies with respect to branch predictor behavior.


The repository contains C++ framework as well as TLA+ framework with similar functionality (TLA+ version has not been updated for a long time). Also, there are some auxiliary scripts to simplify the interaction and also to do some format conversions.

The main part of the work was done in C++.

## Building C++

C++ sources are stored in */cpp_version* subdirectory and are build via cmake. The recommended way of building is:

```sh
cd cpp_version
mkdir -p build
cd build
cmake ..
make
```

This builds the project and stores the targets in */cpp_version/build*.

> NOTE: Some scripts that work with C++ assume that the targets are in this location.

There are 5 targets:
- **compare_traces** - generates a pair of execution traces from input
- **exhaustive_search** - searches the state space for TAs
- **random_search** - randomly generates inputs and trying to find TA
- **event_table** - step-by-step resolution process
- **exec_prog** (legacy)

More about the usage of these targets is described down the text.

## Constructing a Pair of Traces

The most tested feature of the framework is generation of the pair of traces based on input file.

Usage:

```sh
./cpp_version/build/compare_traces filename
```

The program prints a pair of traces to stdout.

> NOTE: you simply can run *compare-traces.sh* providing input file name

### Input

Input represents the sequence of instructions that enter the processor pipeline. Each line in input file represents such an instruction. The line starts with functional unit assigned to the instruction, that comes the optional tag (`#tagname`), after goes the list of dependencies (`@tagname`). In the end of the line FU latency has to be specified. `[t]` if latency is the same for both executions. `[t1|t2]` if need to specify different execution times for 2 execution traces.

The misprediction region is defined with indentation.

Example of input:
```
FU1 #1 [4|1]
FU2 @1 [4]
FU2 #2 [4]
FU1 @2 [4]
```

It produces the following output:
```
	1	2	3	4	5	6	7	8	9	10	11	12	13	14	15
1	IF	ID	FU1	FU1	FU1	FU1	COM	
2		IF	ID	rs2	rs2	rs2	rs2	rs2	FU2	FU2	FU2	FU2	COM	
3			IF	ID	FU2	FU2	FU2	FU2	rob	rob	rob	rob	rob	COM	
4				IF	ID	rs1	rs1	rs1	FU1	FU1	FU1	FU1	rob	rob	COM	
--------------------------------------------------------------------
	1	2	3	4	5	6	7	8	9	10	11	12	13	14	15	16
1	IF	ID	FU1	COM	
2		IF	ID	FU2	FU2	FU2	FU2	COM	
3			IF	ID	rs2	rs2	rs2	FU2	FU2	FU2	FU2	COM	
4				IF	ID	rs1	rs1	rs1	rs1	rs1	rs1	FU1	FU1	FU1	FU1	COM	

Deps:
1 -> 2
3 -> 4
```

More examples of inputs and outputs can be found in */examples* folder.


## Randomized search

Needed for searching TA examples. The entry point is *random_search.cpp*.

Generates random input pairs and verifies the desired property on them. See the parameters of random input config in structure `RandomProgConfig` in *Prog.h*.

The current property to verify is `has_TA()` function which is also defined in *Prog.h* and implemented in *Prog.cpp*. The property simply compares the execution steps of the two traces.

## State space exploration

Iterates through every possible input within a set of constraints (size, number of dependencies). See *exhaustive_search.h*.

As well as randomized search no user interface, so the constraints are to be specified in `total_search_TA` function.

# Output formats and visualization

how to color outputs

syntax highlight for .instr

drawio converter