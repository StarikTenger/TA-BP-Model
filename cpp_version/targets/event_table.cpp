#include "PipelineState.h"
#include "TraceDiagonal.h"
#include "EventTable.h"

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

    vector<Instr> prog_alt = read_program(filename, true);
    print_program(prog_alt);
    cout << endl;

    EventTable event_table;
    event_table.fromProg(prog);
    event_table.print();

    for (int i = 0; event_table.resolution_step(prog_alt) && i < 20; i++) {
        cout << "\n";
        event_table.print();
    }
}