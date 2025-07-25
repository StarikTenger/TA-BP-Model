#include "EventTable.h"
#include "TraceDiagonal.h"
#include "Util.h"

using namespace std;

bool Event::operator<(const Event& other) const {
    return std::tie(instr, type) < std::tie(other.instr, other.type);
}

bool Event::operator==(const Event& other) const {
    return instr == other.instr && type == other.type;
}

bool Event::operator!=(const Event& other) const {
    return !(*this == other);
}

EventTable::EventTable(int numInstructions) {
    table.resize(numInstructions, vector<int>(EVENT_NUM, -1));
}

void EventTable::setEvent(int instruction, EventType eventType, int timeStamp) {
    table[instruction][eventType] = timeStamp;
}

int EventTable::getEvent(int instruction, EventType eventType) {
    return table[instruction][eventType];
}

bool EventTable::operator==(const EventTable& other) const {
    return table == other.table;
}

bool EventTable::operator!=(const EventTable& other) const {
    return !(*this == other);
}

void EventTable::fromProg(const std::vector<Instr>& prog) {
    table.resize(prog.size(), std::vector<int>(EVENT_NUM, -1));

    TraceDiagonal trace(prog);

    for (int i = 0; i < prog.size(); i++) {
        for (int cc = 0; cc < trace.length_cc(); cc++) {
            if (trace.get(i, cc) == IF && trace.get(i, cc - 1) != IF) {
                setEvent(i, IF_Acq, cc);
            }
            if (trace.get(i, cc) != IF && trace.get(i, cc - 1) == IF) {
                setEvent(i, IF_Rel, cc);
            }
            if (trace.get(i, cc) == ID && trace.get(i, cc - 1) != ID) {
                setEvent(i, ID_Acq, cc);
            }
            if (trace.get(i, cc) != ID && trace.get(i, cc - 1) == ID) {
                setEvent(i, ID_Rel, cc);
            }
            if (trace.get(i, cc) == FU && trace.get(i, cc - 1) != FU) {
                setEvent(i, FU_Acq, cc);
            }
            if (trace.get(i, cc) != FU && trace.get(i, cc - 1) == FU) {
                setEvent(i, FU_Rel, cc);
            }
            if (trace.get(i, cc) == COM && trace.get(i, cc - 1) != COM) {
                setEvent(i, Event_COM, cc);
            }
            if (trace.get(i, cc) == SQUASHED && trace.get(i, cc - 1) != SQUASHED) {
                setEvent(i, Event_Squashed, cc);
            }
        }
    }
}

void EventTable::print() const {

    // Map event types to names
    static const std::map<int, std::string> event_names = {
        {IF_Acq, "IF_a"}, {IF_Rel, "IF_r"},
        {ID_Acq, "ID_a"}, {ID_Rel, "ID_r"},
        {FU_Acq, "FU_a"}, {FU_Rel, "FU_r"},
        {Event_COM, "COM"}, {Event_Squashed, "Sq"}
    };

    if (!connections.empty()) {
        for (const auto& entry : connections.back()) {
            // Print dependency sets
            for (const auto& dep_set : entry.second) {
                std::cout << "{";
                bool first = true;
                for (const auto& ev : dep_set) {
                    if (!first) std::cout << ", ";
                    std::cout << "[" << ev.instr + 1 << ", " << event_names.at(ev.type) << "]";
                    first = false;
                }
                std::cout << "}";
                // Print arrow and target event
                std::cout << " -> [" << entry.first.instr + 1 << ", " << event_names.at(entry.first.type) << "]" << std::endl;
            }
            
        }
    }

    std::cout << "   IF_a\tIF_r\tID_a\tID_r\tFU_a\tFU_r\tCOM\tSq" << std::endl;
    for (int i = 0; i < table.size(); i++) { 
        std::cout << i + 1 << ": ";
        for (int j = 0; j < EVENT_NUM; j++) {
            std::cout << table[i][j] << "\t\t";
        }
        std::cout << std::endl;
    }
}

bool check_constraints(const std::vector<std::vector<int>>& table, const std::vector<Instr>& prog, int instr, int event_type, int event_time) {
    if (event_type == IF_Acq) {
        if (instr == 0) return true;
        return table[instr - 1][IF_Rel] == -1 || event_time >= table[instr - 1][IF_Rel];
    } else if (event_type == IF_Rel) {
        return event_time > table[instr][IF_Acq];
    } else if (event_type == ID_Acq) {
        return (event_time >= table[instr][IF_Rel]) &&
            (instr == 0 || event_time >= table[instr - 1][ID_Rel]);
    } else if (event_type == ID_Rel) {
        return event_time > table[instr][ID_Acq];
    } else if (event_type == FU_Acq) {
        // Check that FU_Acq >= ID_Rel
        if (event_time < table[instr][ID_Rel]) {
            return false;
        }
        // Check data dependencies: all dependencies' FU_Rel <= this FU_Acq
        const Instr& current = prog[instr];
        for (int dep : current.data_deps) {
            if (dep >= 0 && table[dep][FU_Rel] > event_time) {
                return false;
            }
        }
        
        for (int i = 0; i < prog.size(); ++i) {
            if (i == instr) continue;
            const Instr& other = prog[i];
            if (other.fu_type == current.fu_type) {
                // Check if other's FU_Acq <= this FU_Acq < other's FU_Rel
                int other_acq = table[i][FU_Acq];
                int other_rel = table[i][FU_Rel];
                int this_acq = event_time;
                if (other_acq != -1 && 
                    other_rel != -1 &&
                    (other_acq <= this_acq && i < instr ||
                    other_acq < this_acq && i > instr) && 
                    this_acq < other_rel) {
                    return false;
                }
            }
        }
        return true;
    } else if (event_type == FU_Rel) {
        return event_time == table[instr][FU_Acq] + prog[instr].lat_fu;
    } else if (event_type == Event_COM) {
        return (event_time >= table[instr][FU_Rel]) &&
            (instr == 0 || event_time > table[instr - 1][Event_COM]);
    } else if (event_type == Event_Squashed) {
        // TODO
    }
    return true;
}

int where_event(const std::vector<Instr>& prog, Event event, const vector<vector<int>>& table, 
    const vector<tuple<int, int, int>>& upd_reversed, const vector<bool>& mask) 
{
    std::vector<std::vector<int>> new_table = table;
    for (size_t i = 0; i < upd_reversed.size(); ++i) {
        if (!mask[i]) {
            int instr, event_type, new_time;
            std::tie(instr, event_type, new_time) = upd_reversed[i];
            new_table[instr][event_type] = new_time;
        }
    }

    int new_time = 0;
    while (!check_constraints(new_table, prog, event.instr, event.type, new_time)) {
        ++new_time;
    }
    return new_time;

}

int EventTable::resolution_step(const std::vector<Instr>& prog) {
    int conflict_count = 0;
    std::vector<std::tuple<int, int, int>> updates; // (instr, event_type, new_time)

    for (int instr = 0; instr < table.size(); ++instr) {
        for (int event_type = 0; event_type < EVENT_NUM; ++event_type) {
            int current_time = table[instr][event_type];
            if (current_time == -1) continue;
            int new_time = 0;
            while (!check_constraints(table, prog, instr, event_type, new_time)) {
                ++new_time;
            }
            if (new_time != current_time) {
                ++conflict_count;
                updates.emplace_back(instr, event_type, new_time);
            }
        }
    }

    connections.push_back({});

    if (last_update_reversed.size()) {
        for (const auto& upd : updates) {
            int instr, event_type, new_time;
            std::tie(instr, event_type, new_time) = upd;

            MaskGenerator mask_gen(last_update_reversed.size());
            do {
                int time = where_event(prog, {instr, event_type}, table, last_update_reversed, mask_gen.get_mask());
                if (time == new_time) {
                    Event update_event{instr, event_type};
                    std::set<Event> events_from_mask;
                    for (size_t i = 0; i < last_update_reversed.size(); ++i) {
                        if (mask_gen.get_mask()[i]) {
                            int dep_instr, dep_event_type, dep_time;
                            std::tie(dep_instr, dep_event_type, dep_time) = last_update_reversed[i];
                            events_from_mask.insert(Event{dep_instr, dep_event_type});
                        }
                    }
                    if (connections.back().find(update_event) == connections.back().end()) {
                        connections.back()[update_event] = {};
                    }
                    connections.back()[update_event].insert(events_from_mask);
                    mask_gen.restrict_last();
                }
            } while (mask_gen.next());
        }
    }

    last_update_reversed.clear();
    // Apply all updates at once
    for (const auto& upd : updates) {
        int instr, event_type, new_time;
        std::tie(instr, event_type, new_time) = upd;
        last_update_reversed.emplace_back(instr, event_type, table[instr][event_type]);
        table[instr][event_type] = new_time;
    }

    return conflict_count;
}

std::vector<std::vector<std::set<std::set<Event>>>> EventTable::extract_graph() const{
    // Create a causality graph: for each event, a set of incomming multiedges
    
    // Initialize the graph structure
    std::vector<std::vector<std::set<std::set<Event>>>> graph(table.size());
    for (int instr = 0; instr < table.size(); instr++) {
        graph[instr].resize(EVENT_NUM); 
    }

    // Fill the graph with connections
    for (const auto& con_step : connections) {
        for (const auto& entry : con_step) {
            const Event& event = entry.first;
            const std::set<std::set<Event>>& deps = entry.second;

            // Add the event to the graph
            for (const auto& dep_set : deps) {
                graph[event.instr][event.type].insert(dep_set);
            }
        }
    }

    // Print the causality graph
    static const std::map<int, std::string> event_names = {
        {IF_Acq, "IF_a"}, {IF_Rel, "IF_r"},
        {ID_Acq, "ID_a"}, {ID_Rel, "ID_r"},
        {FU_Acq, "FU_a"}, {FU_Rel, "FU_r"},
        {Event_COM, "COM"}, {Event_Squashed, "Sq"}
    };

    // std::cout << "Causality Graph:" << std::endl;
    // for (int instr = 0; instr < graph.size(); ++instr) {
    //     for (int event_type = 0; event_type < graph[instr].size(); ++event_type) {
    //         for (const auto& dep_set : graph[instr][event_type]) {
    //             std::cout << "{";
    //             bool first = true;
    //             for (const auto& ev : dep_set) {
    //                 if (!first) std::cout << ", ";
    //                 std::cout << "[" << ev.instr + 1 << ", " << event_names.at(ev.type) << "]";
    //                 first = false;
    //             }
    //             std::cout << "} -> [" << instr + 1 << ", " << event_names.at(event_type) << "]" << std::endl;
    //         }
    //     }
    // }

    return graph;
}
