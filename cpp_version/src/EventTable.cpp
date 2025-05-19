#include "EventTable.h"
#include "TraceDiagonal.h"

using namespace std;

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

void EventTable::fromProg(std::vector<Instr>& prog) {
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
        cout << endl;
    }
}

void EventTable::print() const {
    std::cout << "   IF_a\tIF_r\tID_a\tID_r\tFU_a\tFU_r\tCOM\tSq" << std::endl;
    for (int i = 0; i < table.size(); i++) {
        std::cout << i + 1 << ": ";
        for (int j = 0; j < EVENT_NUM; j++) {
            std::cout << table[i][j] << "\t";
        }
        std::cout << std::endl;
    }
}