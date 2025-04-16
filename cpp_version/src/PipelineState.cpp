#include "PipelineState.h"

using namespace std;

PipelineState::PipelineState() {
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

string PipelineState::formatted_string() {
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

bool PipelineState::next(const vector<Instr> &prog)
{
    // Commit stage
    for (int i = 0; i < SUPERSCALAR; i++) {
        if (stage_COM[i] != -1) {
            completed = stage_COM[i];
            stage_COM[i] = -1;
        }
    }

    // Execute stage
    for (int i = 0; i < FU_NUM; i++) {
        if (stage_FU[i].cycles_left > 0) {
            stage_FU[i].cycles_left--;
        }
        if (stage_FU[i].cycles_left == 0 && stage_FU[i].idx != -1) {
            // Squash next instrucions
            for (int j = 0; j < prog[stage_FU[i].idx].mispred_region; j++) {
                squashed.insert(stage_FU[i].idx + 1 + j);
            }

            executed.insert(stage_FU[i].idx);
            stage_FU[i].idx = -1;
        }
    }

    // From ROB to commit stage
    for (int i = 0; i < SUPERSCALAR; i++) {
        while (!ROB.empty() && squashed.contains(ROB.front())) {
            ROB.pop_front();
        }

        if (!ROB.empty() && executed.contains(ROB.front())) {
            int rob_entry = ROB.front();
            ROB.pop_front();
            stage_COM[i] = rob_entry;
        }
    }

    // Squash instructions in the pipeline
    for (int i = 0; i < SUPERSCALAR; i++) {
        if (stage_ID[i] != -1 && squashed.contains(stage_ID[i])) {
            stage_ID[i] = -1;
        }
    }
    for (int i = 0; i < FU_NUM; i++) {
        if (stage_FU[i].idx != -1 && squashed.contains(stage_FU[i].idx)) {
            stage_FU[i].idx = -1;
        }
    }
    for (int i = 0; i < SUPERSCALAR; i++) {
        if (stage_IF[i].idx != -1 && squashed.contains(stage_IF[i].idx)) {
            stage_IF[i].idx = -1;
        }
    }
    for (int i = 0; i < FU_NUM; i++) {
        for (auto it = stage_RS[i].begin(); it != stage_RS[i].end();) {
            if (squashed.contains(*it)) {
                it = stage_RS[i].erase(it);
            } else {
                ++it;
            }
        }
    }
    // Move PC to the next non-squashed instruction
    while (pc < prog.size() && squashed.contains(pc)) {
        pc++;
    }

    // From rs to FU stage
    for (int i = 0; i < FU_NUM; i++) {
        if (stage_FU[i].idx == -1) {
            bool found = false;
            for (auto rs_entry : stage_RS[i]) {
                bool deps_resolved = true;
                for (int dep : prog[rs_entry].data_deps) {
                    if (!executed.contains(dep)) {
                        deps_resolved = false;
                        break;
                    }
                }
                if (deps_resolved) {
                    stage_FU[i].idx = rs_entry;
                    stage_FU[i].cycles_left = prog[rs_entry].lat_fu;
                    stage_RS[i].erase(rs_entry);
                    found = true;
                    break;
                }
            }

            if (found) continue;

            for (int s = 0; s < SUPERSCALAR; s++) {
                int id_entry = stage_ID[s];
                if (id_entry != -1 && prog[id_entry].fu_type == i) {
                    bool deps_resolved = true;
                    for (int dep : prog[id_entry].data_deps) {
                        if (!executed.contains(dep)) {
                            deps_resolved = false;
                            break;
                        }
                    }
                    if (deps_resolved) {
                        stage_FU[i].idx = id_entry;
                        stage_FU[i].cycles_left = prog[id_entry].lat_fu;
                        stage_ID[s] = -1;
                        ROB.push_back(id_entry);
                        break;
                    }
                }
            }
        }
    }

    // From ID to rs stage
    for (int i = 0; i < SUPERSCALAR; i++) {
        if (stage_ID[i] != -1) {
            int id_entry = stage_ID[i];
            ROB.push_back(id_entry);
            stage_ID[i] = -1;
            stage_RS[prog[id_entry].fu_type].insert(id_entry);
        }
    }

    // From IF to ID stage
    for (int i = 0; i < SUPERSCALAR; i++) {
        if (stage_IF[i].cycles_left > 0) {
            stage_IF[i].cycles_left--;
        }
        if (stage_IF[i].cycles_left == 0 && stage_IF[i].idx != -1) {
            stage_ID[i] = stage_IF[i].idx;
            stage_IF[i].idx = -1;
        }
    }
    
    // Fetch next instruction
    for (int i = 0; i < SUPERSCALAR; i++) {
        if (stage_IF[i].idx == -1) {
            if (pc < prog.size()) {
                stage_IF[i].idx = pc;
                stage_IF[i].cycles_left = 1;
                pc++;
            }
        }
    }

    for (int i = 0; i < SUPERSCALAR; i++) {
        if (stage_IF[i].idx != -1 && prog[stage_IF[i].idx].br_pred) {
            pc = stage_IF[i].idx + prog[stage_IF[i].idx].mispred_region + 1;
            
        }
    }

    clock_cycle++;

    return completed >= (int)prog.size() - 1;
}

ostream& operator<<(ostream& os, const PipelineState& state) {
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