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

int main(int argc, char *argv[]) 
{
    if (argc < 2) {
        cerr << "Usage: " << argv[0] << " <program_file>" << endl;
        return 1;
    }
    string filename = argv[1];
    vector<Instr> prog = read_program(filename);
    if (prog.empty()) {
        cerr << "No instructions found in the program file." << endl;
        return 1;
    }

    print_program(prog);

    PipelineState state;
    state.clock_cycle = 0;
    state.pc = 0;

    bool ta = has_TA(prog);

    if (ta) {
        cerr << "The program has a timing anomaly." << endl;
    } else {
        cerr << "The program does not have a timing anomaly." << endl;
    }
    
    {
        ofstream outfile("out1.tmp");
        if (outfile.is_open()) {
            outfile << dump_trace(prog);
            outfile.close();
            cerr << "Trace dumped to out1.tmp" << endl;
        } else {
            cerr << "Failed to open file for writing trace." << endl;
        }
    }

    for (auto& instr : prog) {
        instr.br_pred = false;
    }

    {
        ofstream outfile("out2.tmp");
        if (outfile.is_open()) {
            outfile << dump_trace(prog);
            outfile.close();
            cerr << "Trace dumped to out2.tmp" << endl;
        } else {
            cerr << "Failed to open file for writing trace." << endl;
        }
    }

    return 0;
}