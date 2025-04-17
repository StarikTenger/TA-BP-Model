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
    int fu_type = 0;
    int lat_fu = 1;
    std::set<int> data_deps;
    int mispred_region = 0;
    bool br_pred = false;
};

std::vector<Instr> read_program(const std::string& filename);

void print_program(const std::vector<Instr>& prog);

void misprediction_on(std::vector<Instr>& prog);

void misprediction_off(std::vector<Instr>& prog);

std::vector<Instr> random_program(int size);

std::string dump_trace(const std::vector<Instr>& prog);

bool has_TA(std::vector<Instr>& prog);

std::set<int> unused_instrs(const std::vector<Instr>& prog);

void remove_unused(std::vector<Instr>& prog);

void dump_pair_of_traces(std::vector<Instr> prog, std::string filename1, std::string filename2);