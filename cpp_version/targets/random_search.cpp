#include "PipelineState.h"

#include <iostream>
#include <vector>
#include <algorithm>
#include <set>
#include <map>
#include <deque>
#include <fstream>
#include <sstream>

using namespace std;

void random_search_TA() 
{
    int iterations = 10000000;
    int size = 4;
    for (int i = 0; i < iterations; i++) {
        vector<Instr> prog = random_program(size);
        PipelineState state;
        
        if (has_TA(prog)) {
            cerr << "Found a timing anomaly" << endl;

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
        srand(time(0));
    }

    random_search_TA();

    return 0;
}