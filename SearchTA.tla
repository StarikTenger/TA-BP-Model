---- MODULE SearchTA ----
EXTENDS TLC, Sequences, Integers, Util, FiniteSets

VARIABLES StageIF_1, StageID_1, StageRS_1, StageFU_1, StageCOM_1
VARIABLE ROB_1, Ready_1
VARIABLE Squashed_1
VARIABLE Commited_1
VARIABLE PC_1
VARIABLE ClockCycle_1

VARIABLES StageIF_2, StageID_2, StageRS_2, StageFU_2, StageCOM_2
VARIABLE ROB_2, Ready_2
VARIABLE Squashed_2
VARIABLE Commited_2
VARIABLE PC_2
VARIABLE ClockCycle_2


Prog1 == ⟨
[idx |-> 1,     type |-> "FU1",    data_deps |-> {},    spec_of |-> {},  br_pred |-> {},       LatIF |-> {1},  LatFU |-> {4}]
⟩

Prog2 == ⟨
[idx |-> 1,     type |-> "FU1",    data_deps |-> {},    spec_of |-> {},  br_pred |-> {},       LatIF |-> {1},  LatFU |-> {5}]
⟩

Pipe1 == INSTANCE Pipeline WITH 
    prog <- Prog1,
    superscalar <- 1,
    BranchDivergence <- FALSE,
    StageIF <- StageIF_1,
    StageID <- StageID_1,
    StageRS <- StageRS_1,
    StageFU <- StageFU_1,
    StageCOM <- StageCOM_1,
    ROB <- ROB_1,
    Ready <- Ready_1,
    Squashed <- Squashed_1,
    Commited <- Commited_1,
    PC <- PC_1,
    ClockCycle <- ClockCycle_1

Pipe2 == INSTANCE Pipeline WITH 
    prog <- Prog2,
    superscalar <- 1,
    BranchDivergence <- FALSE,
    StageIF <- StageIF_2,
    StageID <- StageID_2,
    StageRS <- StageRS_2,
    StageFU <- StageFU_2,
    StageCOM <- StageCOM_2,
    ROB <- ROB_2,
    Ready <- Ready_2,
    Squashed <- Squashed_2,
    Commited <- Commited_2,
    PC <- PC_2,
    ClockCycle <- ClockCycle_2


Init ==
    /\ Pipe1!Init
    /\ Pipe2!Init

Next ==
    /\ Pipe1!Next
    /\ Pipe2!Next

NoTA ==
    ¬(Pipe1!ExecutionFinished /\ Pipe2!ExecutionFinished /\ ClockCycle_1 < ClockCycle_2) 

====