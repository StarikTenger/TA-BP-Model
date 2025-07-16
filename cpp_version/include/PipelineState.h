/* 
 * This file contains PipelineState structure that represents the state of the pipeline.
 * PipelineState represents which stages are processing which instructions.
 * next() function advances the pipeline by one clock cycle.
 */

#pragma once

#include "Prog.h"

#include <iostream>
#include <vector>
#include <algorithm>
#include <set>
#include <map>
#include <deque>
#include <fstream>
#include <sstream>
#include <cstdlib>

const int SUPERSCALAR = 1;
const int FU_NUM = 4;

struct StageEntry
{
    int idx = -1;
    int cycles_left = 0;
};

struct PipelineState
{
    int clock_cycle = 0;
    int pc = 0;

    std::vector<StageEntry> stage_IF = std::vector<StageEntry>(SUPERSCALAR);
    std::vector<int> stage_ID = std::vector<int>(SUPERSCALAR);
    std::vector<std::set<int>> stage_RS = std::vector<std::set<int>>(FU_NUM);
    std::vector<StageEntry> stage_FU = std::vector<StageEntry>(FU_NUM);
    std::vector<int> stage_COM = std::vector<int>(SUPERSCALAR);
    std::deque<int> ROB = std::deque<int>();

    int completed = -1; // The highest index of the instruction that has been completed
    std::set<int> executed; // Instructions that have been executed
    std::set<int> squashed; // Instructions that have been squashed
    std::vector<int> branch_stack; // Stack of branch instructions
    
    PipelineState();

    // Serializes the state to a TLA+ format string
    std::string formatted_string();

    // Human-readable output for debugging
    friend std::ostream& operator<<(std::ostream& os, const PipelineState& state);

    // Advances the pipeline by one clock cycle. Takes a program as input.
    bool next(const std::vector<Instr>& prog);
};