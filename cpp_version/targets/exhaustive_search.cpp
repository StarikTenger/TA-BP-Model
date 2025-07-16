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
#include <chrono>
#include <unordered_set>

using namespace std;

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
    using namespace std::chrono;
    auto start = high_resolution_clock::now();
    int TA_counter = 0;

    unordered_set<string> explored_TAs;

    int size = 4;
    int mispred_size = 4;
    vector<int> types(size + mispred_size);
    vector<int> type_bounds(size + mispred_size, FU_NUM - 1);
    vector<int> fu_lats = {4, 4};
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
                prog[before_spec - 1].fu_type = 0;
                prog[before_spec - 1].mispred_region = mispred_size;

                for (int i = 0; i < mispred_size; i++) {
                    Instr instr;
                    instr.fu_type = types[size + i];
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
                    string serialized = TraceDiagonal(prog).serizlize();
                    if (explored_TAs.find(serialized) != explored_TAs.end()) {
                        continue; // Skip already explored trace
                    }

                    cerr << "Found a timing anomaly" << endl;

                    misprediction_on(prog);
                    remove_unused(prog);

                    print_program(prog);

                    explored_TAs.insert(serialized);
                    cerr << "Trace Diagonal:\n" << TraceDiagonal(prog).serizlize() << endl;

                    // dump_pair_of_traces(prog, "out1.tmp", "out2.tmp");

                    // return;

                    TA_counter++;
                }

            }
        } while (deps_next(deps, size));
    } while (vector_next(types, type_bounds));
    
    auto end = high_resolution_clock::now();
    auto duration = duration_cast<milliseconds>(end - start).count();
    cout << "Checked " << count << " programs. Found " << TA_counter << " TAs" << endl;
    cout << "Elapsed time: " << duration << " ms" << endl;
}

int main(int argc, char *argv[]) 
{
    total_search_TA();
    
    return 0;
}