#include "PipelineState.h"
#include "TraceDiagonal.h"

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

    cerr << "Original" << endl;
    print_program(prog);
    cout << endl;

    vector<Instr> prog_alt = read_program(filename, true);
    cerr << "Alternative" << endl;
    print_program(prog_alt);

    TraceDiagonal trace_diag(prog);
    cout << trace_diag.serizlize();

    TraceDiagonal trace_diag_alt(prog_alt);

    for (int i = 0; i < max(trace_diag.length_cc(), trace_diag_alt.length_cc()) + 1; i++) {
        cout << "----";
    }
    cout << endl;

    cout << trace_diag_alt.serizlize();

    cout << endl;
    cout << "Deps:" << endl;

    for (int i = 0; i < prog.size(); i++) {
        for (auto dep : prog[i].data_deps) {
            if (dep < i) {
                cout << dep + 1 << " -> " << i + 1 << endl;
            }
        }
    }
}