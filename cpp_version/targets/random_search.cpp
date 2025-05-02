#include "PipelineState.h"
#include "Util.h"

#include <iostream>
#include <vector>
#include <algorithm>
#include <set>
#include <map>
#include <deque>
#include <fstream>
#include <sstream>

using namespace std;

vector<Instr> random_program(int size) {
    vector<int> fu_lats = {4, 4};

    int before_spec = random_int(1, size - 1);
    int after_spec = size - before_spec;
    int spec = 20;

    vector<Instr> prog;

    for (int i = 0; i < before_spec; i++) {
        Instr instr;
        instr.fu_type = random_int(0, FU_NUM - 1);
        instr.lat_fu = fu_lats[instr.fu_type];
        instr.mispred_region = 0;

        prog.push_back(instr);
    }
    prog[before_spec - 1].lat_fu = 1;
    prog[before_spec - 1].mispred_region = spec;

    for (int i = 0; i < spec; i++) {
        Instr instr;
        instr.fu_type = random_int(0, FU_NUM - 1);
        instr.lat_fu = fu_lats[instr.fu_type];
        instr.mispred_region = 0;

        prog.push_back(instr);
    }

    for (int i = 0; i < after_spec; i++) {
        Instr instr;
        instr.fu_type = random_int(0, FU_NUM - 1);
        instr.lat_fu = fu_lats[instr.fu_type];
        instr.mispred_region = 0;

        prog.push_back(instr);
    }

    int deps = 2;
    for (int i = 0; i < deps; i++) {
        int from = random_int(0, prog.size() - 2);
        int to = random_int(from + 1, prog.size() - 1);
        if (from < before_spec || from >= before_spec + spec) {
            prog[to].data_deps.insert(from);
        }
    }

    return prog;
}

bool has_TA2(vector<Instr>& prog)
{
    misprediction_on(prog);

    PipelineState state;
    state.clock_cycle = 0;
    state.pc = 0;

   

    int mispred_start = -1;
    int mispred_end = -1;
    for (int i = 0; i < prog.size(); i++) {
        if (prog[i].mispred_region) {
            mispred_start = i + 1;
            mispred_end = i + 1 + prog[i].mispred_region;
            break;
        }
    }

    bool spec_run_found = false;
    for (int i = 0; !state.next(prog) && i < 100; i++) {
        if (state.pc >= mispred_start && state.pc < mispred_end) {
            for (const auto& entry : state.stage_FU) {
                if (entry.idx >= mispred_start && entry.idx < mispred_end) {
                    spec_run_found = true;
                    break;
                }
            }
        }
    }

    int time1 = state.clock_cycle;

    state = PipelineState();
    state.clock_cycle = 0;
    state.pc = 0;

    

    misprediction_off(prog);

    for (int i = 0; !state.next(prog) && i < 100; i++) {}

    int time2 = state.clock_cycle;

    return spec_run_found && time1 < time2;
}

void random_search_TA() 
{
    int iterations = 10000000;
    int size = 6;
    for (int i = 0; i < iterations; i++) {
        vector<Instr> prog = random_program(size);
        PipelineState state;
        
        if (has_TA2(prog)) {
            cerr << "Found a timing anomaly" << endl;

            print_program(prog);

            misprediction_on(prog);
            remove_unused(prog);

            dump_pair_of_traces(prog, "out1.tmp", "out2.tmp");

            break;
        }

        if (i % 100000 == 0) {
            cerr << "Iteration: " << i << ", No timing anomaly found" << endl;
        }
    }
}

int main(int argc, char *argv[]) 
{
    
    if (argc > 1) {
        int seed = atoi(argv[1]);
        srand(seed);
        cerr << "Using seed: " << seed << endl;
    } else {
        cerr << "No seed provided. Using default seed." << endl;
        auto seed = time(0);
        cerr << "Random seed: " << seed << endl;
        srand(seed);
    }

    random_search_TA();

    return 0;
}