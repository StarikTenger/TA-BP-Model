---- MODULE SearchTA ----
EXTENDS TLC, Sequences, Integers, Util, FiniteSets, FiniteSetsExt, SequencesExt

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

VARIABLES Prog1, Prog2

Pipe1 == INSTANCE Pipeline WITH 
    prog_const <- ⟨⟩,
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
    prog_const <- ⟨⟩,
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

TypeOK_1 == Pipe1!TypeOK
TypeOK_2 == Pipe2!TypeOK

\* TODO: find a better way to catch stalled forever pipe
CCBound_1 == ClockCycle_1 <= 70
CCBound_2 == ClockCycle_2 <= 70

BeforeSpec == 2
SpecLen == 10
AfterSpec == 3

ProgLen == BeforeSpec + SpecLen + AfterSpec

BasicLat == 4
DepNumber == 2

\* 3 instr
\* 10 spec, all same
\* 2 more instr

ChooseProg ==
    ∃ lat_FU1 ∈ {4,5,6,7} :
    ∃ lat_FU2 ∈ {4,5,6,7} :
    ∃ types ∈ CartProd([i ∈ 1..BeforeSpec + AfterSpec |-> {"FU1", "FU2"}]) :
    ∃ lats ∈ CartProd([i ∈ 1..BeforeSpec + AfterSpec |-> {
        IF types[i] = "FU1" THEN lat_FU1 ELSE lat_FU2
    }]) :
    ∃ dep_set ∈ kSubset(DepNumber * 2, 1..BeforeSpec ∪ (BeforeSpec + SpecLen + 1)..ProgLen) :
    LET dep_seq == SetToSeq(dep_set) IN
    Prog1 = 
        [
            [i ∈ 1..BeforeSpec |-> [
            idx |-> i,
            type |-> types[i],
            data_deps |-> {},
            spec_of |-> {},
            br_pred |-> {},
            LatIF |-> {1},  
            LatFU |-> {lats[i]}]] ∘

            [i ∈ 1..SpecLen |-> [
            idx |-> BeforeSpec + i,
            type |-> "FU1",
            data_deps |-> {},
            spec_of |-> {BeforeSpec},
            br_pred |-> {FALSE},
            LatIF |-> {1},  
            LatFU |-> {BasicLat}]] ∘

            [i ∈ 1..AfterSpec |-> [
            idx |-> BeforeSpec + SpecLen + i,
            type |-> types[BeforeSpec + i],
            data_deps |-> {},
            spec_of |-> {},
            br_pred |-> {},
            LatIF |-> {1},  
            LatFU |-> {lats[BeforeSpec + i]}]]

        EXCEPT \* TODO ! HARDCODE !
            ![dep_seq[2]].data_deps = {dep_seq[1]},
            ![dep_seq[4]].data_deps = {dep_seq[3]}
        ]

AlterProg ==
    Prog2 = [i ∈ 1..ProgLen |-> [Prog1[i] EXCEPT !.br_pred = {TRUE}]]
    \* ∃ i ∈ 1..ProgLen :
    \* Prog2 = [Prog1 EXCEPT ![i].LatFU = {1}]

Init ==
    /\ ChooseProg
    /\ AlterProg
    /\ Pipe1!PartialInit
    /\ Pipe2!PartialInit

Next ==
    /\ Pipe1!Next
    /\ Pipe2!Next

NoTA ==
    ¬(Pipe1!ExecutionFinished /\ Pipe2!ExecutionFinished /\ ClockCycle_1 < ClockCycle_2) 

====