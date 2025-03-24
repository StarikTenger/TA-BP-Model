---- MODULE TestBench ----
EXTENDS TLC, Pipeline

const_prog ==
⟨
    \* Change LatFU to 1 in instr1 to see TA
    [idx |-> 1, type |-> "BR", data_deps |-> {}, spec_of |-> {}, LatIF |-> 1, LatFU |-> 5],
    [idx |-> 2, type |-> "MEM", data_deps |-> {}, spec_of |-> {1}, LatIF |-> 1, LatFU |-> 1],
    [idx |-> 3, type |-> "ALU", data_deps |-> {}, spec_of |-> {1}, LatIF |-> 1, LatFU |-> 1],
    [idx |-> 4, type |-> "ALU", data_deps |-> {}, spec_of |-> {1}, LatIF |-> 1, LatFU |-> 1],
    [idx |-> 5, type |-> "ALU", data_deps |-> {}, spec_of |-> {1}, LatIF |-> 1, LatFU |-> 1],
    [idx |-> 6, type |-> "ALU", data_deps |-> {}, spec_of |-> {}, LatIF |-> 1, LatFU |-> 1]
⟩

const_superscalar == 2


====