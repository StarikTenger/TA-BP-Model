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

    cout << "--------------------------------------------------------------------\n";

    TraceDiagonal trace_diag_alt(prog_alt);
    cout << trace_diag_alt.serizlize();
}