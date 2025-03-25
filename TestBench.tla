---- MODULE TestBench ----
EXTENDS TLC, Pipeline

const_prog ==
⟨
    \* Change LatFU to 1 in instr1 to see TA
    [idx |-> 1, type |-> "MEM", data_deps |-> {}, spec_of |-> {}, LatIF |-> 1, LatFU |-> 1],
    [idx |-> 2, type |-> "BR_MEM",  data_deps |-> {}, spec_of |-> {}, LatIF |-> 1, LatFU |-> 1],
        [idx |-> 3, type |-> "ALU", data_deps |-> {}, spec_of |-> {2}, LatIF |-> 1, LatFU |-> 1],
        [idx |-> 4, type |-> "BR_ALU",  data_deps |-> {}, spec_of |-> {2}, LatIF |-> 1, LatFU |-> 1],
            [idx |-> 5, type |-> "ALU", data_deps |-> {}, spec_of |-> {2,4}, LatIF |-> 1, LatFU |-> 1],
            [idx |-> 6, type |-> "ALU", data_deps |-> {}, spec_of |-> {2,4}, LatIF |-> 1, LatFU |-> 1],
        [idx |-> 7, type |-> "ALU", data_deps |-> {}, spec_of |-> {2}, LatIF |-> 1, LatFU |-> 1],
    [idx |-> 8, type |-> "ALU", data_deps |-> {}, spec_of |-> {}, LatIF |-> 1, LatFU |-> 1]
⟩

const_superscalar == 1


====