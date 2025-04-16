#include "PipelineState.h"

#include <iostream>
#include <vector>
#include <algorithm>
#include <set>
#include <map>
#include <deque>
#include <fstream>
#include <sstream>

using namespace std;

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