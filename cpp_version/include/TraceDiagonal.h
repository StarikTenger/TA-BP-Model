#pragma once

#include "Prog.h"

#include <vector>
#include <string>

enum InstrProgress {
    NONE = 0,
    IF,
    ID,
    RS,
    FU,
    ROB,
    COM,
    DONE,
    SQUASHED
};

class TraceDiagonal {
public:
    static const int SPACING = 100;

    TraceDiagonal(const std::vector<Instr>& prog);

    int get(int instr, int cycle) const;

    std::string serizlize() const;

    int length_cc() const;

    bool operator<(const TraceDiagonal& other) const;

private:
    
    struct Row {
        int offset;
        std::vector<int> res;
    };

    std::vector<Row> table;
};