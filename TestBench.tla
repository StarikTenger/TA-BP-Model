---- MODULE TestBench ----
EXTENDS TLC, Pipeline

const_prog ==
⟨
    \* Change LatFU to 1 in instr1 to see TA
    [idx |-> 1, type |-> "MEM", data_deps |-> {}, control_deps |-> {}, LatIF |-> 1, LatFU |-> 1],
    [idx |-> 2, type |-> "ALU", data_deps |-> {1}, control_deps |-> {}, LatIF |-> 1, LatFU |-> 4],
    [idx |-> 3, type |-> "ALU", data_deps |-> {}, control_deps |-> {}, LatIF |-> 1, LatFU |-> 4],
    [idx |-> 4, type |-> "MEM", data_deps |-> {3}, control_deps |-> {}, LatIF |-> 1, LatFU |-> 4]
⟩

const_superscalar == 1


====