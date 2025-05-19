#pragma once

#include "Prog.h"
#include "PipelineState.h"

#include <vector>
#include <set>

enum EventType {
    IF_Acq = 0,
    IF_Rel,
    ID_Acq,
    ID_Rel,
    FU_Acq,
    FU_Rel,
    Event_COM,
    Event_Squashed,
    EVENT_NUM // A count of the events
};


struct EventTable {
    // (Instruction -> EventType -> TimeStamp) mapping
    std::vector<std::vector<int>> table;

    EventTable(int numInstructions = 0);

    void setEvent(int instruction, EventType eventType, int timeStamp);

    int getEvent(int instruction, EventType eventType);

    bool operator==(const EventTable& other) const;

    void fromProg(std::vector<Instr>& prog);

    void print() const;
};