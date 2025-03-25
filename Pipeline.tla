---- MODULE Pipeline ----
EXTENDS TLC, Sequences, Integers, Util, FiniteSets

CONSTANT prog, superscalar

VARIABLES StageIF, StageID, StageRS, StageFU, StageCOM

VARIABLE ROB, Ready

VARIABLE Squashed

VARIABLE ClockCycle

\* idxuction number to fetch next
VARIABLE PC

\* idxuction types
InstrTypes == {"ALU", "MEM", "BR_ALU", "BR_MEM"}
BranchInstr == {"BR_ALU", "BR_MEM"}

FuncUnits == {"ALU", "LSU"}

\* Chose FU for idxuction of a given type
ChooseFu(type) ==
    CASE type = "ALU" -> "ALU"
      [] type = "MEM" -> "LSU"
      [] type = "BR_ALU" -> "ALU"
      [] type = "BR_MEM" -> "LSU"


\* Type safety invariant
TypeOK == 
    /\ prog ∈ Seq([
        idx: Positive, 
        type: InstrTypes, 
        data_deps: SUBSET Positive, 
        spec_of: SUBSET Positive, 
        LatIF: SUBSET Positive, 
        LatFU: SUBSET Positive
        ])
    /\ superscalar ∈ Positive
    /\ PC ∈ Nat
    /\ StageIF ∈ [1..superscalar -> SUBSET [idx: Positive, cycles_left: Positive]]
    /\ StageID ∈ [1..superscalar -> SUBSET Positive]
    /\ StageRS ∈ [FuncUnits -> SUBSET Positive]
    /\ StageFU ∈ [FuncUnits -> SUBSET [idx: Positive, cycles_left: Positive]]
    /\ StageCOM ∈ [1..superscalar -> SUBSET Positive]

    /\ ∀ s ∈ 1..superscalar :  
        /\ Cardinality(StageIF[s]) <= 1
        /\ Cardinality(StageID[s]) <= 1
        /\ Cardinality(StageCOM[s]) <= 1

    /\ ∀ fu ∈ FuncUnits : 
        \* /\ Cardinality(StageRS[fu]) <= ??? - We do not have restriction for RS capacity now
        /\ Cardinality(StageFU[fu]) <= 1

    /\ ROB ∈ Seq(Positive)
    /\ Ready ∈ SUBSET Positive
    /\ Squashed ∈ SUBSET Positive


\* We assume that RS are infinite, so ID can always progress
CanProgressID == TRUE

CanProgressIF == 
    /\ CanProgressID  
    /\ ∀ instr ∈ AllInSeq(StageIF) : instr.cycles_left = 1

SquashIF(stage) ==
    [s ∈ 1..superscalar |-> {entry ∈ stage[s] : entry.idx ∉ Squashed'}]    

AllLatIF == CartProd([i ∈ 1..Len(prog) |-> prog[i].LatIF])

NextIF ==
    ∃ lats ∈ AllLatIF :
    StageIF' = SquashIF(
    IF CanProgressIF
    THEN 
        [
            s ∈ 1..superscalar |-> 
            IF PC' - 1 + s > Len(prog)
            THEN {}
            ELSE
              {[idx |-> PC' - 1 + s, 
                cycles_left |-> lats[PC' - 1 + s]]}
        ]
    ELSE 
        [
            s ∈ 1..superscalar |-> 
            {[entry EXCEPT !.cycles_left = Decrement(@)] : entry ∈ StageIF[s]}
        ]
    )

SquashID(stage) ==
    [s ∈ 1..superscalar |-> {entry ∈ stage[s] : entry ∉ Squashed'}]

NextID == \* TODO: fix it, not sure that correct
    StageID' = SquashID(
    IF CanProgressIF
    THEN [i ∈ 1..superscalar |-> {entry.idx : entry ∈ StageIF[i]}]
    ELSE [i ∈ 1..superscalar |-> {}]
    )

\*                     Map                                            Filter
EnterRS(fu) == {i ∈ {entry : entry ∈ AllInSeq(StageID)} : ChooseFu(prog[i].type) = fu}

\* FU is busy next cycle
BusyFU(fu) == ∃ entry ∈ StageFU[fu] : entry.cycles_left > 1

EnterFU(fu) == 
    LET with_resolved_dep == {
        idx ∈ StageRS[fu] ∪ {i ∈ AllInSeq(StageID) : ChooseFu(prog[i].type) = fu} : 
        (∀ dep ∈ prog[idx].data_deps : dep ∈ Ready)}
    IN
    IF /\ ¬BusyFU(fu) \* FU is not busy
       /\ with_resolved_dep /= {} \* Can only take task with resolved dependencies
    THEN 
        {CHOOSE idx ∈ with_resolved_dep : ∀ idx1 ∈ with_resolved_dep : idx <= idx1}
    ELSE 
        {}



SquashRS(stage) ==
    [fu ∈ FuncUnits |-> {entry ∈ stage[fu] : entry ∉ Squashed'}]

NextRS ==
    StageRS' = SquashRS([fu ∈ FuncUnits |-> (StageRS[fu] ∪ EnterRS(fu)) \ EnterFU(fu)])

SquashFU(stage) ==
    [fu ∈ FuncUnits |-> {entry ∈ stage[fu] : entry.idx ∉ Squashed'}]

AllLatFU == CartProd([i ∈ 1..Len(prog) |-> prog[i].LatFU])

NextFU ==
    ∃ lats ∈ AllLatFU :
    StageFU' = SquashFU(
        [fu ∈ FuncUnits |-> 
            IF BusyFU(fu)
            THEN {[entry EXCEPT !.cycles_left = Decrement(@)] : entry ∈ StageFU[fu]}
            ELSE {[idx |-> entry, cycles_left |-> lats[entry]] : entry ∈ EnterFU(fu)}
        ]
    )

NextReady ==
    Ready' = Ready ∪ {
        entry.idx : entry ∈ 
        {
            entry ∈ UNION {StageFU'[fu] : fu ∈ FuncUnits} :
            entry.cycles_left = 1
        }
    }    

CommitNumber ==
    Min({superscalar, Len(ROB)})

CanCommit ==
    LET commit_number == Min({superscalar, Len(ROB)}) IN
    commit_number > 0 /\ ∀ s ∈ 1..commit_number : ROB[s] ∈ Ready /\ prog[ROB[s]].spec_of = {}

NextROB ==
    ROB' = Erase(
    LET RobAppend == \* TODO: this does not allow bubbles in ID stage:
    IF CanProgressID /\ ∃ s ∈ 1..superscalar : StageID[s] /= {}
    THEN ROB ∘ FlattenSeq(StageID)
    ELSE ROB
    IN
    IF CanCommit
    THEN DropHead(RobAppend, CommitNumber)
    ELSE RobAppend
    ,Squashed')
    

NextCOM ==
    IF CanCommit
    THEN StageCOM' = 
        [s ∈ 1..CommitNumber |-> {ROB[s]}] ∘ 
        [s ∈ 1..(superscalar - CommitNumber) |-> {}]
    ELSE StageCOM' = [s ∈ 1..superscalar |-> {}]
    

SquashedBy(idx) == {i ∈ 1..Len(prog) : idx ∈ prog[i].spec_of}

NextSquashed ==
    Squashed' = 
        Squashed ∪ 
        UNION {
            SquashedBy(entry.idx) : 
            entry ∈ {
                entry ∈ UNION {StageFU[fu] : fu ∈ FuncUnits } : 
                prog[entry.idx].type ∈ BranchInstr /\ entry.cycles_left = 1
            }
        }

RECURSIVE next_valid(_)
next_valid(i) ==
    IF i > Len(prog) \/ i ∉ Squashed'
    THEN i
    ELSE next_valid(i + 1)

NextPC ==
    PC' = 
        IF PC = 0 THEN 1 ELSE
        IF PC <= Len(prog) /\ CanProgressIF 
        THEN next_valid(PC + superscalar)
        ELSE PC

ExecutionFinished ==
    UNCHANGED ⟨StageIF, StageID, StageRS, StageFU, ROB, StageCOM⟩

NextClockCycle ==
    ClockCycle' = IF ExecutionFinished THEN ClockCycle ELSE ClockCycle + 1

Init == 
    /\ PC = 0
    /\ StageIF = [s ∈ 1..superscalar |-> {}]
    /\ StageID = [s ∈ 1..superscalar |-> {}]
    /\ StageRS = [fu ∈ FuncUnits |-> {}]
    /\ StageFU = [fu ∈ FuncUnits |-> {}]
    /\ StageCOM = [s ∈ 1..superscalar |-> {}]
    /\ ROB = ⟨⟩
    /\ Ready = {}
    /\ Squashed = {}
    /\ ClockCycle = 0
    
Next == 
    /\ NextSquashed
    /\ NextPC

    /\ NextIF
    /\ NextID
    /\ NextRS
    /\ NextFU

    /\ NextCOM
    /\ NextROB
    /\ NextReady
    /\ NextClockCycle

\* NextCOM
\* NextROB

====