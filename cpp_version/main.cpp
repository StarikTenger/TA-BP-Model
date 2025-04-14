#include <iostream>
#include <vector>
#include <algorithm>
#include <set>
#include <map>
#include <deque>
#include <fstream>
#include <sstream>
#include <cstdlib>

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

    string formatted_string() {
        stringstream ss;
        ss << "/\\ Ready = {";
        for (const auto& exec : executed) {
            ss << exec << " ";
        }
        ss << "}\n";

        ss << "/\\ Squashed = {}\n"; // Placeholder for squashed instructions if needed

        ss << "/\\ StageIF = <<";
        for (const auto& entry : stage_IF) {
            if (entry.idx != -1) {
            ss << "{[idx |-> " << entry.idx << ", cycles_left |-> " << entry.cycles_left << "]} ";
            }
        }
        ss << ">>\n";

        ss << "/\\ StageID = <<";
        for (const auto& id : stage_ID) {
            if (id != -1) {
            ss << "{" << id << "} ";
            }
        }
        ss << ">>\n";

        ss << "/\\ StageRS = [";
        for (size_t i = 0; i < stage_RS.size(); ++i) {
            ss << "FU" << (i + 1) << " |-> {";
            for (const auto& elem : stage_RS[i]) {
            ss << elem << " ";
            }
            ss << "}";
            if (i < stage_RS.size() - 1) ss << ", ";
        }
        ss << "]\n";

        ss << "/\\ StageFU = [";
        for (size_t i = 0; i < stage_FU.size(); ++i) {
            ss << "FU" << (i + 1) << " |-> ";
            if (stage_FU[i].idx != -1) {
            ss << "{[idx |-> " << stage_FU[i].idx << ", cycles_left |-> " << stage_FU[i].cycles_left << "]}";
            } else {
            ss << "{}";
            }
            if (i < stage_FU.size() - 1) ss << ", ";
        }
        ss << "]\n";

        ss << "/\\ ROB = <<";
        for (const auto& rob_entry : ROB) {
            ss << rob_entry << " ";
        }
        ss << ">>\n";
        

        ss << "/\\ StageCOM = <<";
        for (const auto& com : stage_COM) {
            if (com != -1) {
            ss << "{" << com << "} ";
            }
        }
        ss << ">>\n";

        ss << "/\\ ClockCycle = " << clock_cycle << "\n";
        ss << "/\\ PC = " << pc << "\n";
        ss << "/\\ Commited = {" << completed << "}\n";

        return ss.str();
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

    state.clock_cycle++;

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

void  misprediction_on(vector<Instr>& prog) 
{
    for (auto& instr : prog) {
        instr.br_pred = false;
    }
}

void  misprediction_off(vector<Instr>& prog) 
{
    for (auto& instr : prog) {
        instr.br_pred = true;
    }
}

bool has_TA(vector<Instr>& prog)
{
    misprediction_on(prog);

    PipelineState state;
    state.clock_cycle = 0;
    state.pc = 0;

    for (int i = 0; !next_state(state, prog) && i < 100; i++) {}

    int time1 = state.clock_cycle;

    state = PipelineState();
    state.clock_cycle = 0;
    state.pc = 0;

    misprediction_off(prog);

    for (int i = 0; !next_state(state, prog) && i < 100; i++) {}

    int time2 = state.clock_cycle;

    return time1 < time2;
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

        if (next_state(state, prog)) {
            break;
        }
        
        state.clock_cycle++;
    }

    return trace.str();
}

int random_int(int min, int max) {
    return rand() % (max - min + 1) + min;
}

vector<Instr> random_program(int size) {
    vector<int> fu_lats = {4, 7};

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

set<int> unused_instrs(const vector<Instr>& prog) {
    set<int> unused;

    for (int i = 0; i < prog.size(); i++) {
        unused.insert(i);
    }
    
    PipelineState state;

    for (int i = 0; !next_state(state, prog) && i < 100; i++) {
        for (const auto& entry : state.stage_IF) {
            if (entry.idx != -1) {
                unused.erase(entry.idx);
            }
        }
    }

    return unused;
}

void remove_unused(vector<Instr>& prog) {
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

            print_program(prog);

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

            misprediction_off(prog);

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

            break;
        }

        if (i % 100000 == 0) {
            cerr << "Iteration: " << i << ", No timing anomaly found" << endl;
        }
    }
}

bool vector_next(vector<int>& v, vector<int>& max) 
{
    for (int i = v.size() - 1; i >= 0; i--) {
        if (v[i] < max[i]) {
            v[i]++;
            return true;
        } else {
            v[i] = 0;
        }
    }
    return false;
}

bool deps_next(vector<pair<int, int>>& deps, int prog_len) 
{
    int n = prog_len;
    int size = deps.size();

    for (int i = size - 1; i >= 0; i--) {
        int& a = deps[i].first;
        int& b = deps[i].second;

        if (b < n - 1) {
            b++;
            bool out_of_bounds = false;
            for (int j = i + 1; j < size; j++) {
                deps[j].first = deps[i].first;
                deps[j].second = deps[i].second + 1 + (j - i - 1);
            }

            for (int j = 0; j < size; j++) {
                if (deps[j].second >= n) {
                    out_of_bounds = true;
                }
            }

            if (out_of_bounds) {
                return deps_next(deps, prog_len);
            }
            return true;
        } else if (a < n - 2) {
            a++;
            b = a + 1;
            bool out_of_bounds = false;
            for (int j = i + 1; j < size; j++) {
                deps[j].first = deps[i].first;
                deps[j].second = deps[i].second + 1 + (j - i - 1);
            }

            for (int j = 0; j < size; j++) {
                if (deps[j].second >= n) {
                    out_of_bounds = true;
                }
            }

            if (out_of_bounds) {
                return deps_next(deps, prog_len);
            }
            return true;
        }
    }

    return false;
}

void total_search_TA() 
{
    int size = 3;
    vector<int> types(size);
    vector<int> type_bounds(size, FU_NUM - 1);
    vector<int> fu_lats = {4, 4};
    int mispred_size = 20;
    int count = 0;

    do {
        vector<pair<int, int>> deps = {{0,1}};
        do {
            for (int before_spec = 1; before_spec < size; before_spec++) {
                int after_spec = size - before_spec;
                vector<Instr> prog;

                for (int i = 0; i < before_spec; i++) {
                    Instr instr;
                    instr.fu_type = types[i];
                    instr.lat_fu = fu_lats[instr.fu_type];
                    instr.mispred_region = 0;

                    prog.push_back(instr);
                }
                prog[before_spec - 1].lat_fu = 1;
                prog[before_spec - 1].mispred_region = mispred_size;

                for (int i = 0; i < mispred_size; i++) {
                    Instr instr;
                    instr.fu_type = 0;
                    instr.lat_fu = fu_lats[instr.fu_type];
                    instr.mispred_region = 0;

                    prog.push_back(instr);
                }

                for (int i = 0; i < after_spec; i++) {
                    Instr instr;
                    instr.fu_type = types[before_spec + i];
                    instr.lat_fu = fu_lats[instr.fu_type];
                    instr.mispred_region = 0;

                    prog.push_back(instr);
                }

                for (int i = 0; i < deps.size(); i++) {
                    int from = deps[i].first;
                    int to = deps[i].second;
                    if (from >= before_spec) from += mispred_size;
                    if (to >= before_spec) to += mispred_size;
                    prog[to].data_deps.insert(from);
                }

                count++;
                if (count % 100000 == 0) {
                    cerr << "Iteration: " << count << ", No timing anomaly found" << endl;
                }

                if (has_TA(prog)) {
                    cerr << "Found a timing anomaly" << endl;

                    misprediction_on(prog);
                    remove_unused(prog);

                    print_program(prog);

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

                    misprediction_off(prog);

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

                    return;
                }

            }
        } while (deps_next(deps, size));
    } while (vector_next(types, type_bounds));
    
    cout << "Checked " << count << " programs. No TA found" << endl;
}

int main(int argc, char *argv[]) 
{
    // if (argc < 2) {
    //     cerr << "Usage: " << argv[0] << " <program_file>" << endl;
    //     return 1;
    // }
    // string filename = argv[1];
    // vector<Instr> prog = read_program(filename);
    // if (prog.empty()) {
    //     cerr << "No instructions found in the program file." << endl;
    //     return 1;
    // }

    // print_program(prog);

    // PipelineState state;
    // state.clock_cycle = 0;
    // state.pc = 0;

    // bool ta = has_TA(prog);

    // if (ta) {
    //     cerr << "The program has a timing anomaly." << endl;
    // } else {
    //     cerr << "The program does not have a timing anomaly." << endl;
    // }
    
    // {
    //     ofstream outfile("out1.tmp");
    //     if (outfile.is_open()) {
    //         outfile << dump_trace(prog);
    //         outfile.close();
    //         cerr << "Trace dumped to out1.tmp" << endl;
    //     } else {
    //         cerr << "Failed to open file for writing trace." << endl;
    //     }
    // }

    // for (auto& instr : prog) {
    //     instr.br_pred = false;
    // }

    // {
    //     ofstream outfile("out2.tmp");
    //     if (outfile.is_open()) {
    //         outfile << dump_trace(prog);
    //         outfile.close();
    //         cerr << "Trace dumped to out2.tmp" << endl;
    //     } else {
    //         cerr << "Failed to open file for writing trace." << endl;
    //     }
    // }

    // if (argc > 1) {
    //     int seed = atoi(argv[1]);
    //     srand(seed);
    //     cerr << "Using seed: " << seed << endl;
    // } else {
    //     cerr << "No seed provided. Using default seed." << endl;
    //     srand(time(0));
    // }

    // random_search_TA();

    // vector<pair<int, int>> deps = {{0,1}, {0,2}};
    // int prog_len = 4;


    // int i = 0;
    // do {
    //     i++;
    //     cout << i << ": ";
    //     for (const auto& dep : deps) {
    //         cout << "" << dep.first << " -> " << dep.second << "; ";
    //     }
    //     cout << endl;
    // } while (deps_next(deps, prog_len));

    // cout << "\n";

    // int n = prog_len;
    // i = 0;
    // for (int a = 0; a < n - 2; a++) {
    //     for (int b = a + 1; b < n; b++) {
    //         for (int c = a; c < n - 1; c++) {
    //             for (int d = a == c ? b + 1 : c + 1; d < n; d++) {
    //                 i++;
    //                 cout << i << ": " << a << " -> " << b << "; " << c << " -> " << d << endl;
    //             }
    //         }
    //     }
    // }

    total_search_TA();


    return 0;
}