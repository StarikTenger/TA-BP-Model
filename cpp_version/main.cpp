#include <iostream>
#include <vector>
#include <algorithm>
#include <set>
#include <map>
#include <deque>
#include <fstream>
#include <sstream>

using namespace std;

const int SUPERSCALAR = 1;
const int FU_NUM = 2;

struct StageEntry
{
    int idx = -1;
    int cycles_left = 0;
};

struct PipelineState
{
    int clock_cycle = 0;
    int pc = 0;
    vector<StageEntry> stage_IF = vector<StageEntry>(SUPERSCALAR);
    vector<int> stage_ID = vector<int>(SUPERSCALAR);
    vector<set<int>> stage_RS = vector<set<int>>(FU_NUM);
    vector<StageEntry> stage_FU = vector<StageEntry>(FU_NUM);
    vector<int> stage_COM = vector<int>(SUPERSCALAR);
    deque<int> ROB = deque<int>();
    int completed = -1; // The highest index of the instruction that has been completed
    set<int> executed; // Instructions that have been executed
    set<int> squashed; // Instructions that have been squashed

    PipelineState() {
        for (auto& entry : stage_IF) {
            entry = {-1, 0};
        }
        fill(stage_ID.begin(), stage_ID.end(), -1);
        for (auto& rs : stage_RS) {
            rs.clear();
        }
        for (auto& entry : stage_FU) {
            entry = {-1, 0};
        }
        fill(stage_COM.begin(), stage_COM.end(), -1);
    } 

    void formatted_print() {
        cout << "/\\ Ready = {";
        for (const auto& exec : executed) {
            cout << exec << " ";
        }
        cout << "}\n";

        cout << "/\\ Squashed = {}\n"; // Placeholder for squashed instructions if needed

        cout << "/\\ StageRS = [";
        for (size_t i = 0; i < stage_RS.size(); ++i) {
            cout << "FU" << (i + 1) << " |-> {";
            for (const auto& elem : stage_RS[i]) {
            cout << elem << " ";
            }
            cout << "}";
            if (i < stage_RS.size() - 1) cout << ", ";
        }
        cout << "]\n";

        cout << "/\\ StageFU = [";
        for (size_t i = 0; i < stage_FU.size(); ++i) {
            cout << "FU" << (i + 1) << " |-> ";
            if (stage_FU[i].idx != -1) {
            cout << "{[idx |-> " << stage_FU[i].idx << ", cycles_left |-> " << stage_FU[i].cycles_left << "]}";
            } else {
            cout << "{}";
            }
            if (i < stage_FU.size() - 1) cout << ", ";
        }
        cout << "]\n";

        cout << "/\\ ROB = <<";
        for (const auto& rob_entry : ROB) {
            cout << rob_entry << " ";
        }
        cout << ">>\n";

        cout << "/\\ StageID = <<";
        for (const auto& id : stage_ID) {
            if (id != -1) {
            cout << "{" << id << "} ";
            }
        }
        cout << ">>\n";

        cout << "/\\ StageIF = <<";
        for (const auto& entry : stage_IF) {
            if (entry.idx != -1) {
            cout << "{[idx |-> " << entry.idx << ", cycles_left |-> " << entry.cycles_left << "]} ";
            }
        }
        cout << ">>\n";

        cout << "/\\ StageCOM = <<";
        for (const auto& com : stage_COM) {
            if (com != -1) {
            cout << "{" << com << "} ";
            }
        }
        cout << ">>\n";

        cout << "/\\ ClockCycle = " << clock_cycle << "\n";
        cout << "/\\ PC = " << pc << "\n";
        cout << "/\\ Commited = {" << completed << "}\n";
    }

    friend ostream& operator<<(ostream& os, const PipelineState& state) {
        os << "Clock Cycle: " << state.clock_cycle << "\n";
        os << "Program Counter: " << state.pc << "\n";

        os << "Stage IF: ";
        for (const auto& entry : state.stage_IF) {
            os << "{idx: " << entry.idx << ", cycles_left: " << entry.cycles_left << "} ";
        }
        os << "\n";

        os << "Stage ID: ";
        for (const auto& id : state.stage_ID) {
            os << id << " ";
        }
        os << "\n";

        os << "Stage RS: ";
        for (const auto& rs : state.stage_RS) {
            os << "{";
            for (const auto& elem : rs) {
                os << elem << " ";
            }
            os << "} ";
        }
        os << "\n";

        os << "Stage FU: ";
        for (const auto& entry : state.stage_FU) {
            os << "{idx: " << entry.idx << ", cycles_left: " << entry.cycles_left << "} ";
        }
        os << "\n";

        os << "Stage COM: ";
        for (const auto& com : state.stage_COM) {
            os << com << " ";
        }
        os << "\n";

        os << "ROB: ";
        for (const auto& rob_entry : state.ROB) {
            os << rob_entry << " ";
        }
        os << "\n";

        os << "Executed: ";
        for (const auto& exec : state.executed) {
            os << exec << " ";
        }
        os << "\n";

        os << "Completed: " << state.completed << "\n";

        return os;
    }
};

struct Instr
{
    int fu_type = 0;
    int lat_fu = 1;
    set<int> data_deps;
    int mispred_region = 0;
    bool br_pred = false;
};

bool next_state(PipelineState& state, vector<Instr> prog) 
{
    // Commit stage
    for (int i = 0; i < SUPERSCALAR; i++) {
        if (state.stage_COM[i] != -1) {
            state.completed = state.stage_COM[i];
            state.stage_COM[i] = -1;
        }
    }

    // Execute stage
    for (int i = 0; i < FU_NUM; i++) {
        if (state.stage_FU[i].cycles_left > 0) {
            state.stage_FU[i].cycles_left--;
        }
        if (state.stage_FU[i].cycles_left == 0 && state.stage_FU[i].idx != -1) {
            // Squash next instrucions
            for (int j = 0; j < prog[state.stage_FU[i].idx].mispred_region; j++) {
                state.squashed.insert(state.stage_FU[i].idx + 1 + j);
            }

            state.executed.insert(state.stage_FU[i].idx);
            state.stage_FU[i].idx = -1;
        }
    }

    // From ROB to commit stage
    for (int i = 0; i < SUPERSCALAR; i++) {
        while (!state.ROB.empty() && state.squashed.contains(state.ROB.front())) {
            state.ROB.pop_front();
        }

        if (!state.ROB.empty() && state.executed.contains(state.ROB.front())) {
            int rob_entry = state.ROB.front();
            state.ROB.pop_front();
            state.stage_COM[i] = rob_entry;
        }
    }

    // Squash instructions in the pipeline
    for (int i = 0; i < SUPERSCALAR; i++) {
        if (state.stage_ID[i] != -1 && state.squashed.contains(state.stage_ID[i])) {
            state.stage_ID[i] = -1;
        }
    }
    for (int i = 0; i < FU_NUM; i++) {
        if (state.stage_FU[i].idx != -1 && state.squashed.contains(state.stage_FU[i].idx)) {
            state.stage_FU[i].idx = -1;
        }
    }
    for (int i = 0; i < SUPERSCALAR; i++) {
        if (state.stage_IF[i].idx != -1 && state.squashed.contains(state.stage_IF[i].idx)) {
            state.stage_IF[i].idx = -1;
        }
    }
    for (int i = 0; i < FU_NUM; i++) {
        for (auto it = state.stage_RS[i].begin(); it != state.stage_RS[i].end();) {
            if (state.squashed.contains(*it)) {
                it = state.stage_RS[i].erase(it);
            } else {
                ++it;
            }
        }
    }
    // Move PC to the next non-squashed instruction
    while (state.pc < prog.size() && state.squashed.contains(state.pc)) {
        state.pc++;
    }

    // From rs to FU stage
    for (int i = 0; i < FU_NUM; i++) {
        if (state.stage_FU[i].idx == -1) {
            bool found = false;
            for (auto rs_entry : state.stage_RS[i]) {
                bool deps_resolved = true;
                for (int dep : prog[rs_entry].data_deps) {
                    if (!state.executed.contains(dep)) {
                        deps_resolved = false;
                        break;
                    }
                }
                if (deps_resolved) {
                    state.stage_FU[i].idx = rs_entry;
                    state.stage_FU[i].cycles_left = prog[rs_entry].lat_fu;
                    state.stage_RS[i].erase(rs_entry);
                    found = true;
                    break;
                }
            }

            if (found) continue;

            for (int s = 0; s < SUPERSCALAR; s++) {
                int id_entry = state.stage_ID[s];
                if (id_entry != -1 && prog[id_entry].fu_type == i) {
                    bool deps_resolved = true;
                    for (int dep : prog[id_entry].data_deps) {
                        if (!state.executed.contains(dep)) {
                            deps_resolved = false;
                            break;
                        }
                    }
                    if (deps_resolved) {
                        state.stage_FU[i].idx = id_entry;
                        state.stage_FU[i].cycles_left = prog[id_entry].lat_fu;
                        state.stage_ID[s] = -1;
                        state.ROB.push_back(id_entry);
                        break;
                    }
                }
            }
        }
    }

    // From ID to rs stage
    for (int i = 0; i < SUPERSCALAR; i++) {
        if (state.stage_ID[i] != -1) {
            int id_entry = state.stage_ID[i];
            state.ROB.push_back(id_entry);
            state.stage_ID[i] = -1;
            state.stage_RS[prog[id_entry].fu_type].insert(id_entry);
        }
    }

    // From IF to ID stage
    for (int i = 0; i < SUPERSCALAR; i++) {
        if (state.stage_IF[i].cycles_left > 0) {
            state.stage_IF[i].cycles_left--;
        }
        if (state.stage_IF[i].cycles_left == 0 && state.stage_IF[i].idx != -1) {
            state.stage_ID[i] = state.stage_IF[i].idx;
            state.stage_IF[i].idx = -1;
        }
    }
    
    // Fetch next instruction
    for (int i = 0; i < SUPERSCALAR; i++) {
        if (state.stage_IF[i].idx == -1) {
            if (state.pc < prog.size()) {
                state.stage_IF[i].idx = state.pc;
                state.stage_IF[i].cycles_left = 1;
                state.pc++;
            }
        }
    }

    for (int i = 0; i < SUPERSCALAR; i++) {
        if (state.stage_IF[i].idx != -1 && prog[state.stage_IF[i].idx].br_pred) {
            state.pc = state.stage_IF[i].idx + prog[state.stage_IF[i].idx].mispred_region + 1;
            
        }
    }

    return state.completed >= (int)prog.size() - 1;

}

vector<Instr> read_program(const string& filename) 
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
                    instr.lat_fu = stoi(token.substr(1, token.size() - 2));
                } else if (token[0] == '#') {
                    label_map[token.substr(1)] = prog.size();
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
    for (size_t i = 0; i < prog.size(); ++i) {
        cerr << i << ": ";
        cerr << "FU" << prog[i].fu_type + 1 << ", Lat = " << prog[i].lat_fu;
        cerr << ", Data Dependencies: {";
        for (const auto& dep : prog[i].data_deps) {
            cerr << dep << " ";
        }
        cerr << "}, \tMisprediction Region: " << prog[i].mispred_region;
        cerr << "\n";
    }
}



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

    for (auto& instr : prog) {
        instr.br_pred = true;
    }

    for (int i = 0; i < 100; i++) {
        // cout << " ======== Clock Cycle: " << state.clock_cycle << " ========\n";
        // cout << state;
        cout << "State " << state.clock_cycle << ":\n";
        state.formatted_print();
        cout << "\n";

        if (next_state(state, prog)) {
            break;
        }
        
        state.clock_cycle++;
    }

    
    return 0;
}