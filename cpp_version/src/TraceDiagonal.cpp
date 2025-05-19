
#include "TraceDiagonal.h"
#include "PipelineState.h"

using namespace std;
 
TraceDiagonal::TraceDiagonal(std::vector<Instr> prog) 
{
    table = vector<Row>(prog.size());

    PipelineState state;
    const int CYCLE_LIMIT = 1000;

    for (int cc = 0; !state.next(prog) && cc < CYCLE_LIMIT; cc++) {
        // Fetch stage
        for (const auto& entry : state.stage_IF) {
            if (entry.idx >= 0) {
                if (!table[entry.idx].res.size()) {
                    table[entry.idx].offset = cc;
                }
                table[entry.idx].res.push_back(IF * SPACING);
            }
        }

        // Decode Stage
        for (const auto& idx : state.stage_ID) {
            if (idx >= 0) {
                table[idx].res.push_back(ID * SPACING);
            }
        }

        // RS Stage
        for (const auto& entry : state.stage_RS) {
            for (const auto& idx : entry) {
                if (idx >= 0) {
                    table[idx].res.push_back(RS * SPACING + prog[idx].fu_type);
                }
            }
        }

        // FU Stage
        for (const auto& entry : state.stage_FU) {
            if (entry.idx >= 0) {
                table[entry.idx].res.push_back(FU * SPACING + prog[entry.idx].fu_type);
            }
        }

        // ROB Stage (pre-commit)
        for (const auto& idx : state.ROB) {
            if (idx >= 0 && state.executed.contains(idx) && !state.squashed.contains(idx)) {
                table[idx].res.push_back(ROB * SPACING);
            }
        }

        // Commit Stage
        for (const auto& idx : state.stage_COM) {
            if (idx >= 0 && state.executed.contains(idx)) {
                table[idx].res.push_back(COM * SPACING);
            }
        }

        // Squashed
        for (const auto& idx : state.squashed) {
            if (idx >= 0 && table[idx].res.size()) {
                table[idx].res.push_back(SQUASHED * SPACING);
            }
        }

        if (cc == CYCLE_LIMIT - 1) {
            cerr << "Reached the limit of " << CYCLE_LIMIT << " cycles" << endl;
        }
    }
}

int TraceDiagonal::get(int instr, int cycle) const
{
    if (instr < 0 || instr >= table.size()) return NONE;
    const auto& row = table[instr];
    int idx = cycle - row.offset;
    if (idx < 0 || idx >= row.res.size()) return NONE;
    return row.res[idx] / SPACING;
}

string TraceDiagonal::serizlize() const
{
    stringstream ss;

    int time_size = 0;
    for (const auto& row : table) {
        if (!row.res.empty()) {
            time_size = max(time_size, static_cast<int>(row.res.size() + row.offset));
        }
    }

    for (int i = 0; i < time_size; i++) {
        ss << "\t" << i + 1;
    }
    ss << endl;
    for (int i = 0; i < table.size(); i++) {
        if (table[i].res.size() == 0) {
            continue;
        }
        ss << i + 1 << "\t";
        for (int j = 0; j < table[i].offset; j++) {
            ss << "\t";
        }
        for (int j = 0; j < table[i].res.size(); j++) {
            switch (table[i].res[j] / SPACING) {
            case IF:
                ss << "IF" << "\t";
                break;
            case ID:
                ss << "ID" << "\t";
                break;
            case RS:
                ss << "rs" << table[i].res[j] % SPACING + 1 << "\t";
                break;
            case FU:
                ss << "FU" << table[i].res[j] % SPACING + 1 << "\t";
                break;
            case ROB:
                ss << "rob" << "\t";
                break;
            case COM:
                ss << "COM" << "\t";
                break;
            case SQUASHED:
                if (table[i].res.size() > 1 && table[i].res[j - 1] / SPACING != SQUASHED) {
                    ss << "#squashed" << "\t";   
                }
                break;
            }
        }
        ss << endl;
    }
    return ss.str();
}

int TraceDiagonal::length_cc() const
{
    return table.back().res.size() + table.back().offset;
}
