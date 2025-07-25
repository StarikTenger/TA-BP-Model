#include "PipelineState.h"
#include "Util.h"
#include "Prog.h"

#include <iostream>
#include <vector>
#include <algorithm>
#include <set>
#include <map>
#include <deque>
#include <fstream>
#include <sstream>

using namespace std;

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
    int size = 4;
    for (int i = 0; i < iterations; i++) {
        RandomProgConfig conf;
        conf.size = 5;
        conf.fu_lats = {4,4};
        conf.mispred_region = true;
        conf.deps = {1,2,3,4};
        vector<Instr> prog = random_program(conf);
        PipelineState state;
        
        if (has_TA(prog)) {
            cerr << "Found a timing anomaly" << endl;
            misprediction_on(prog);
            remove_unused(prog);

            misprediction_off(prog);
            print_program(prog);

            misprediction_on(prog);
            

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