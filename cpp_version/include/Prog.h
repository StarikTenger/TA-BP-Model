/* 
 * This file contains Instr structure that represents an instruction in the pipeline.
 * Program is represented as vector of Instr objects.
 * Also file includes functions to manipuilate with programs, such as reading from a file,
 * printing, generating random programs, and other manipulations.
 */

#pragma once

#include <iostream>
#include <vector>
#include <algorithm>
#include <set>
#include <map>
#include <deque>
#include <fstream>
#include <sstream>
#include <cstdlib>

struct Instr
{
    int fu_type = 0;            // FU assigned
    int lat_fu = 1;             // Cycles spent in FU
    std::set<int> data_deps;    // Data dependencies
    int mispred_region = 0;     // Length of misprediction region, 0 if not a branch
    bool br_pred = false;       // Is branch prediction correct for this instruction?
};

// Reads program from file, set alt to true to read alternative version of
// the program (e.g. latency of  FU1 [4|1] is 4 in the main program and 1 in 
// the alternative)
std::vector<Instr> read_program(const std::string& filename, bool alt = false);

// Print program to stderr
void print_program(const std::vector<Instr>& prog);

// Set br_pred to false for all instructions in the program
void misprediction_on(std::vector<Instr>& prog);

// Set br_pred to true for all instructions in the program
void misprediction_off(std::vector<Instr>& prog);

// Generate random program of given size, other parameters are hardcoded
std::vector<Instr> random_program(int size);

// Checks if porgram with all misprediction is exeuted faster than the one 
// with all correct predictions
bool has_TA(std::vector<Instr>& prog);

// Returns a set of indices of not reachable instructions
std::set<int> unused_instrs(const std::vector<Instr>& prog);

// Removes unreachable instructions from the program
void remove_unused(std::vector<Instr>& prog);

// Dump trace in TLA+ format
std::string dump_trace(const std::vector<Instr>& prog);

// Dumps two traces to files in TLA+ format, first with all mispredictions, second with all correct predictions
void dump_pair_of_traces(std::vector<Instr> prog, std::string filename1, std::string filename2);