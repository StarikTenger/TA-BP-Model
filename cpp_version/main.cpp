#include <iostream>
#include <vector>
#include <algorithm>
#include <set>
#include <deque>

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
    set<int> spec_of;
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
            state.executed.insert(state.stage_FU[i].idx);
            state.stage_FU[i].idx = -1;
        }
    }

    // From ROB to commit stage
    for (int i = 0; i < SUPERSCALAR; i++) {
        if (!state.ROB.empty() && state.executed.contains(state.ROB.front())) {
            int rob_entry = state.ROB.front();
            state.ROB.pop_front();
            state.stage_COM[i] = rob_entry;
        }
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

            if (found) break;

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

    return state.completed >= (int)prog.size() - 1;

}


int main(int argc, char *argv[]) 
{
    vector<Instr> prog = {
        {0, 1, {}, {}, false},
        {1, 2, {0}, {}, false},
        {0, 1, {}, {}, false},
        {1, 2, {2}, {}, false},
        {0, 1, {}, {}, false},
        {1, 2, {4}, {}, false}
    };

    PipelineState state;
    state.clock_cycle = 0;
    state.pc = 0;

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