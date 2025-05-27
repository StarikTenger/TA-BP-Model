#pragma once

#include "Prog.h"
#include "PipelineState.h"

#include <vector>
#include <set>
#include <tuple>

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

struct Event {
    int instr;
    int type;

    bool operator<(const Event& other) const;
};

struct EventTable {
    // (Instruction -> EventType -> TimeStamp) mapping
    std::vector<std::vector<int>> table;
    std::vector<std::tuple<int, int, int>> last_update_reversed;
    std::vector<std::map<Event, std::set<std::set<Event>>>> graph;

    EventTable(int numInstructions = 0);

    void setEvent(int instruction, EventType eventType, int timeStamp);

    int getEvent(int instruction, EventType eventType);

    bool operator==(const EventTable& other) const;

    void fromProg(const std::vector<Instr>& prog);

    void print() const;
    
    // Returns the number of event moved
    int resolution_step(const std::vector<Instr>& prog);
};