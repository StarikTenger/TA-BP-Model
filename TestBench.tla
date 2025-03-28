---- MODULE TestBench ----
EXTENDS TLC, Pipeline
const_prog == ⟨
[idx |-> 1,     type |-> "FU1",         data_deps |-> {},       spec_of |-> {},         LatIF |-> {1},  LatFU |-> {4}],
[idx |-> 2,     type |-> "FU2",         data_deps |-> {},       spec_of |-> {},         LatIF |-> {1},  LatFU |-> {4}],
[idx |-> 3,     type |-> "FU1",         data_deps |-> {2},      spec_of |-> {},         LatIF |-> {1},  LatFU |-> {4}],
[idx |-> 4,     type |-> "FU1",         data_deps |-> {},       spec_of |-> {},         LatIF |-> {1},  LatFU |-> {4}],
[idx |-> 5,     type |-> "FU1",         data_deps |-> {4},      spec_of |-> {},         LatIF |-> {1},  LatFU |-> {4}]
⟩
const_superscalar == 1
const_BranchDivergence == FALSE
TimeBounded == TRUE
====

