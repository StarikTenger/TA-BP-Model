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
    bool operator==(const Event& other) const;
    bool operator!=(const Event& other) const;
};

struct EventTable {
    // (Instruction -> EventType -> TimeStamp) mapping
    std::vector<std::vector<int>> table;
    std::vector<std::tuple<int, int, int>> last_update_reversed;

    // Connections between events derived from resolution steps
    std::vector<std::map<Event, std::set<std::set<Event>>>> connections;

    EventTable(int numInstructions = 0);

    void setEvent(int instruction, EventType eventType, int timeStamp);

    int getEvent(int instruction, EventType eventType);

    bool operator==(const EventTable& other) const;

    bool operator!=(const EventTable& other) const;

    void fromProg(const std::vector<Instr>& prog);

    void print() const;
    
    // Returns the number of events moved
    int resolution_step(const std::vector<Instr>& prog);

    // Returns a causality graph: for each event, a set of incomming multiedges
    std::vector<std::vector<std::set<std::set<Event>>>> extract_graph() const;
};