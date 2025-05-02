#include "Prog.h"
#include "Util.h"
#include "PipelineState.h"

using namespace std;

vector<Instr> read_program(const string& filename, bool alt) 
{
    ifstream file(filename);
    vector<Instr> prog;
    if (file.is_open()) {
        string line;
        map<string, int> label_map;
        vector<int> indentations;

        while (getline(file, line)) {
            if (line.empty()) continue;

            Instr instr;
            size_t pos = 0;

            // Determine indentation level
            int indentation = 0;
            while (pos < line.size() && isspace(line[pos])) {
                if (line[pos] == '\t') {
                    indentation += 4; // Assuming a tab is 4 spaces
                } else {
                    indentation++;
                }
                pos++;
            }
            indentations.push_back(indentation);

            // Tokenize the line using stringstream and operator >>
            vector<string> tokens;
            stringstream ss(line.substr(pos)); // Skip leading spaces
            string token;
            while (ss >> token) {
                tokens.push_back(token);
            }

            // Parse tokens
            for (const auto& token : tokens) {
                if (token.substr(0, 2) == "FU") {
                    instr.fu_type = stoi(token.substr(2)) - 1;
                } else if (token[0] == '@') {
                    instr.data_deps.insert(label_map[token.substr(1)]);
                } else if (token[0] == '[' && token.back() == ']') {
                    if (token.find('|') != string::npos) {
                        size_t delimiter_pos = token.find('|');
                        int n = stoi(token.substr(1, delimiter_pos - 1));
                        int m = stoi(token.substr(delimiter_pos + 1, token.size() - delimiter_pos - 2));
                        instr.lat_fu = alt ? m : n;
                    } else {
                        instr.lat_fu = stoi(token.substr(1, token.size() - 2));
                    }
                } else if (token[0] == '#') {
                    label_map[token.substr(1)] = prog.size();
                } else if (token == "*") {
                    if (alt) {
                        instr.br_pred = true;
                    } else {
                        instr.br_pred = false;
                    }
                }
            }

            prog.push_back(instr);
        }

        // Calculate mispred_region based on indentation
        for (size_t i = 0; i < prog.size(); ++i) {
            int current_indent = indentations[i];
            int mispred_region = 0;
            for (size_t j = i + 1; j < prog.size(); ++j) {
                if (indentations[j] > current_indent) {
                    mispred_region++;
                } else {
                    break;
                }
            }
            prog[i].mispred_region = mispred_region;
        }
    } else {
        cerr << "Unable to open file";
    }
    return prog;
}

void print_program(const vector<Instr>& prog) 
{
    vector<int> mispred_stack;

    for (size_t i = 0; i < prog.size(); ++i) {
        // Print indentation based on the size of the stack
        for (size_t j = 0; j < mispred_stack.size(); ++j) {
            cerr << "    ";
        }

        // Update the misprediction stack
        while (!mispred_stack.empty() && mispred_stack.back() == 0) {
            mispred_stack.pop_back();
        }

        if (prog[i].mispred_region != 0) {
            mispred_stack.push_back(prog[i].mispred_region);
        }

        // Decrease the top of the stack for the current instruction
        if (!mispred_stack.empty()) {
            mispred_stack.back()--;
        }

        

        // Print functional unit type
        cerr << "FU" << prog[i].fu_type + 1;

        // Print label if present
        cerr << " #" << i + 1 << " ";

        // Print data dependencies
        for (const auto& dep : prog[i].data_deps) {
            cerr << "@" << dep + 1 << " ";
        }

        // Print latency
        cerr << "[" << prog[i].lat_fu << "]";

        cerr << "\n";
    }
}

void misprediction_on(vector<Instr>& prog) 
{
    for (auto& instr : prog) {
        instr.br_pred = false;
    }
}

void misprediction_off(vector<Instr>& prog) 
{
    for (auto& instr : prog) {
        instr.br_pred = true;
    }
}

string dump_trace(const vector<Instr>& prog) 
{
    stringstream trace;

    PipelineState state;
    state.clock_cycle = 0;
    state.pc = 0;

    for (int i = 0; i < 100; i++) {
        trace << "State " << state.clock_cycle << ":\n";
        trace << state.formatted_string();
        trace << "\n";

        if (state.next(prog)) {
            break;
        }
        
        state.clock_cycle++;
    }

    return trace.str();
}

bool has_TA(vector<Instr>& prog)
{
    misprediction_on(prog);

    PipelineState state;
    state.clock_cycle = 0;
    state.pc = 0;

    for (int i = 0; !state.next(prog) && i < 100; i++) {}

    int time1 = state.clock_cycle;

    state = PipelineState();
    state.clock_cycle = 0;
    state.pc = 0;

    misprediction_off(prog);

    for (int i = 0; !state.next(prog) && i < 100; i++) {}

    int time2 = state.clock_cycle;

    return time1 < time2;
}

set<int> unused_instrs(const vector<Instr>& prog) 
{
    set<int> unused;

    for (int i = 0; i < prog.size(); i++) {
        unused.insert(i);
    }
    
    PipelineState state;

    for (int i = 0; !state.next(prog) && i < 100; i++) {
        for (const auto& entry : state.stage_IF) {
            if (entry.idx != -1) {
                unused.erase(entry.idx);
            }
        }
    }

    return unused;
}

void remove_unused(vector<Instr>& prog) 
{
    set<int> unused = unused_instrs(prog);
    int deleted = 0;

    vector<int> active_branches;

    for (int i = 0; i < prog.size(); i++) {
            if (unused.contains(i + deleted)) {
            prog.erase(prog.begin() + i);
            i--;
            deleted++;

            for (auto br : active_branches) {
                prog[br].mispred_region--;
            }
        }

        while (active_branches.size() && i > active_branches.back() + prog[active_branches.back()].mispred_region) {
            active_branches.pop_back();
            
        }
        
        if (prog[i].mispred_region) {
            active_branches.push_back(i);
        }

        
    }
}

void dump_pair_of_traces(vector<Instr> prog, std::string filename1, std::string filename2)
{
    misprediction_on(prog);
    remove_unused(prog);

    {
        ofstream outfile(filename1);
        if (outfile.is_open()) {
            outfile << dump_trace(prog);
            outfile.close();
            cerr << "Trace dumped to " << filename1 << endl;
        } else {
            cerr << "Failed to open file for writing trace." << endl;
        }
    }

    misprediction_off(prog);

    {
        ofstream outfile(filename2);
        if (outfile.is_open()) {
            outfile << dump_trace(prog);
            outfile.close();
            cerr << "Trace dumped to " << filename1 << endl;
        } else {
            cerr << "Failed to open file for writing trace." << endl;
        }
    }
}
