---- MODULE TestBench ----
EXTENDS TLC, Pipeline

const_prog ==
⟨
    \* Change LatFU to 1 in instr1 to see TA
    [idx |-> 1, type |-> "MEM", data_deps |-> {}, spec_of |-> {}, LatIF |-> {1,2}, LatFU |-> {1,2}]
⟩

const_superscalar == 1


====