#include "PipelineState.h"
#include "Util.h"
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
    RandomProgConfig conf;
    conf.size = 4;
    conf.fu_lats = {4,4};
    conf.mispred_region = false;
    conf.deps = {2};

    int iterations = 1000000;
    for (int iter = 0; iter < iterations; iter++) {
        // Creating a pair of programs to compare
        // The first program is generated with the given configuration
        // The second program is modified to have a smaller latency for the
        // first instruction
        vector<Instr> prog = random_program(conf);
        vector<Instr> prog_alt = prog;
        prog_alt[0].lat_fu = 1;

        // prog = read_program("/home/stariktenger/Internship2025/TA-BP-model/tmp/input.instr", false);
        // prog_alt = read_program("/home/stariktenger/Internship2025/TA-BP-model/tmp/input.instr", true);

        // Extract event tables from both programs
        EventTable event_table, event_table_alt;
        event_table.fromProg(prog);
        event_table_alt.fromProg(prog_alt);

        // Apply resolution to the first event table
        int step_bound = 50;
        int step = 0;
        for (; 
            step < step_bound && event_table.resolution_step(prog_alt); 
            step++);

        // Verify graph: check reachability of all the moved events
        // 1. Find all moved events in the original program
        set<Event> moved_events;
        for (int instr = 0; instr < prog.size(); instr++) {
            for (int event_type = 0; event_type < EVENT_NUM; event_type++) {
                if (
                    event_table.getEvent(instr, static_cast<EventType>(event_type))
                     != event_table_alt.getEvent(instr, static_cast<EventType>(event_type))) {
                    moved_events.insert({instr, event_type});
                }
            }
        }
        
        // 2. Check if all moved events are reachable in the graph
        auto graph = event_table.extract_graph();

        // Initialize a reversed graph to explore forward
        vector<vector<vector<Event>>> reversed_simplified_graph(graph.size());
        for (int instr = 0; instr < graph.size(); instr++) {
            reversed_simplified_graph[instr].resize(EVENT_NUM);
        }

        // Fill the reversed graph
        for (int instr = 0; instr < graph.size(); instr++) {
            for (int event_type = 0; event_type < EVENT_NUM; event_type++) {
                for (const auto& multiedge : graph[instr][event_type]) {
                    for (const auto& dep_event : multiedge) {
                        reversed_simplified_graph[dep_event.instr][dep_event.type].push_back(Event{instr, event_type});
                    }
                }
            }
        }

        // Check reachability of moved events
        // Visited set to track reachable events
        set<Event> visited;
        deque<Event> queue;

        // Define thge queue and the starting point for BFS
        queue.push_back({0, FU_Rel}); // Start from the variation point
        visited.insert({0, FU_Rel});

        // BFS
        while (!queue.empty()) {
            Event current = queue.front();
            queue.pop_front();

            // Explore all outgoing edges
            for (const auto& next : reversed_simplified_graph[current.instr][current.type]) {
                if (visited.insert(next).second) {
                    queue.push_back(next);
                }
            }
        }

        // Check if all moved events are reachable
        bool all_reachable = true;
        for (const auto& moved_event : moved_events) {
            if (visited.find(moved_event) == visited.end()) {
                cerr << "Moved event [" << moved_event.instr + 1 << ", "
                     << moved_event.type << "] is not reachable in the graph." << endl;
                all_reachable = false;
            }
        }

        static const std::map<int, std::string> event_names = {
            {IF_Acq, "IF_a"}, {IF_Rel, "IF_r"},
            {ID_Acq, "ID_a"}, {ID_Rel, "ID_r"},
            {FU_Acq, "FU_a"}, {FU_Rel, "FU_r"},
            {Event_COM, "COM"}, {Event_Squashed, "Sq"}
        };
        // cout << "Reversed Simplified Graph:" << endl;
        // for (int instr = 0; instr < reversed_simplified_graph.size(); instr++) {
        //     for (int event_type = 0; event_type < reversed_simplified_graph[instr].size(); event_type++) {
        //         if (!reversed_simplified_graph[instr][event_type].empty()) {
        //             cout << "[" << instr + 1 << ", " << event_names.at(event_type) << "] -> ";
        //             for (const auto& next_event : reversed_simplified_graph[instr][event_type]) {
        //                 cout << "[" << next_event.instr + 1 << ", " << event_names.at(next_event.type) << "] ";
        //             }
        //             cout << endl;
        //         }
        //     }
        // }

        // Check if there are any reversed links
        bool has_reversed_connections = false;
        for (int instr = 0; instr < graph.size(); instr++) {
            for (int event_type = 0; event_type < EVENT_NUM; event_type++) {
                for (const auto& multiedge : graph[instr][event_type]) {
                    for (const auto& dep_event : multiedge) {
                        int dep_event_time = event_table.getEvent(dep_event.instr, static_cast<EventType>(dep_event.type));
                        int curr_event_time = event_table.getEvent(instr, static_cast<EventType>(event_type));
                        if (dep_event_time > curr_event_time) {
                            has_reversed_connections = true;
                            cerr << "Reversed connection found: [" << dep_event.instr + 1 << ", "
                                 << event_names.at(dep_event.type) << "] -> ["
                                 << instr + 1 << ", " << event_names.at(event_type) << "]"
                                 << " | times: " << dep_event_time
                                 << " -> " << curr_event_time << endl;
                            break;
                        }
                    }
                }
            }
        }


        if (!all_reachable || has_reversed_connections) {
            cout << "Reversed Simplified Graph:" << endl;
            for (int instr = 0; instr < reversed_simplified_graph.size(); instr++) {
                for (int event_type = 0; event_type < reversed_simplified_graph[instr].size(); event_type++) {
                    if (!reversed_simplified_graph[instr][event_type].empty()) {
                        cout << "[" << instr + 1 << ", " << event_names.at(event_type) << "] -> ";
                        for (const auto& next_event : reversed_simplified_graph[instr][event_type]) {
                            cout << "[" << next_event.instr + 1 << ", " << event_names.at(next_event.type) << "] ";
                        }
                        cout << endl;
                    }
                }
            }

            // Print program
            cerr << "Original Program:" << endl;
            print_program(prog);

            cerr << "Modified Program:" << endl;
            print_program(prog_alt);
            break;
        }
    }

    return 0;
}