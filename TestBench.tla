---- MODULE TestBench ----
EXTENDS TLC, Pipeline

const_prog ==
⟨
    [idx |-> 1, type |-> "ALU", data_deps |-> {}, control_deps |-> {}],
    [idx |-> 2, type |-> "ALU", data_deps |-> {}, control_deps |-> {}],
    [idx |-> 3, type |-> "ALU", data_deps |-> {}, control_deps |-> {}]
⟩

const_superscalar == 2

inv_test == PC /= 6

====