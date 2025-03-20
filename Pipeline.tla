---- MODULE Pipeline ----
EXTENDS TLC, Sequences, Integers, Util, FiniteSets

CONSTANT prog, superscalar

VARIABLES StageIF, StageID, StageRS, StageFU, StageCOM, ROB

\* idxuction number to fetch next
VARIABLE PC

\* idxuction types
InstrTypes == {"ALU", "MEM", "BR"}

FuncUnits == {"ALU", "LSU"}

\* Chose FU for idxuction of a given type
ChooseFu(type) ==
    CASE type = "ALU" -> "ALU"
      [] type = "MEM" -> "LSU"
      [] type = "BR" -> "ALU"

\* Type safety invariant
TypeOK == 
    /\ prog ∈ Seq([idx: Positive, type: InstrTypes, data_deps: SUBSET Positive, control_deps: SUBSET Positive])
    /\ superscalar ∈ Positive
    /\ PC ∈ Positive
    /\ StageIF ∈ [1..superscalar -> SUBSET [idx: Positive, cycles_left: Positive]]
    /\ StageID ∈ [1..superscalar -> SUBSET [idx: Positive]]
    /\ StageRS ∈ [FuncUnits -> SUBSET Positive]
    /\ StageFU ∈ [FuncUnits -> SUBSET [idx: Positive, cycles_left: Positive]]
    /\ StageCOM ∈ [1..superscalar -> SUBSET [idx: Positive]]

    /\ ∀ s ∈ 1..superscalar :  
        /\ Cardinality(StageIF[s]) <= 1
        /\ Cardinality(StageID[s]) <= 1
        /\ Cardinality(StageCOM[s]) <= 1

    /\ ∀ fu ∈ FuncUnits : 
        \* /\ Cardinality(StageRS[fu]) <= ??? - We do not have restriction for RS capacity now
        /\ Cardinality(StageFU[fu]) <= 1

    /\ ROB ∈ Seq([idx: Positive])


\* We assume that RS are infinite, so ID can always progress
CanProgressID == TRUE

CanProgressIF == 
    /\ CanProgressID  
    /\ ∀ instr ∈ AllInSeq(StageIF) : instr.cycles_left = 1

NextIF ==
    IF CanProgressIF
    THEN 
        StageIF' = [
            s ∈ 1..superscalar |-> 
            IF PC - 1 + s > Len(prog)
            THEN {}
            ELSE
              {[idx |-> PC - 1 + s, 
                cycles_left |-> 1]}
        ] \* TODO: add latencies
    ELSE 
        StageIF' = [
            s ∈ 1..superscalar |-> 
            {[entry EXCEPT !.cycles_left = Decrement(@)] : entry ∈ StageIF[s]}
        ]

NextID ==
    IF CanProgressID
    THEN StageID' = [i ∈ 1..superscalar |-> {[idx |-> entry.idx] : entry ∈ StageIF[i]}]
    ELSE StageID' = StageID

\*                     Map                                            Filter
EnterRS(fu) == {i ∈ {entry.idx : entry ∈ AllInSeq(StageIF)} : ChooseFu(prog[i].type) = fu}

Done == {} \* TODO

\* FU is busy next cycle
BusyFU(fu) == ∃ entry ∈ StageFU[fu] : entry.cycles_left > 1

ExitRS(fu) == 
    LET with_resolved_dep == {idx ∈ StageRS[fu] : (∀ dep ∈ prog[idx].data_deps : dep ∈ Done)}
    IN
    IF /\ ¬BusyFU(fu) \* FU is not busy
       /\ with_resolved_dep /= {} \* Can only take task with resolved dependencies
    THEN 
        {CHOOSE idx ∈ with_resolved_dep : ∀ idx1 ∈ with_resolved_dep : idx >= idx1}
    ELSE 
        {}


NextRS ==
    StageRS' = [fu ∈ FuncUnits |-> (StageRS[fu] ∪ EnterRS(fu)) \ ExitRS(fu)]

NextFU ==
    StageFU' = [
        fu ∈ FuncUnits |-> 
        IF BusyFU(fu)
        THEN {[entry EXCEPT !.cycles_left = Decrement(@)] : entry ∈ StageFU[fu]}
        ELSE {[idx |-> entry, cycles_left |-> 3] : entry ∈ ExitRS(fu)} \* TODO: proper latency
    ]

NextPC ==
    PC' = IF PC <= Len(prog) THEN PC + superscalar ELSE PC

Init == 
    /\ PC = 1
    /\ StageIF = [s ∈ 1..superscalar |-> {}]
    /\ StageID = [s ∈ 1..superscalar |-> {}]
    /\ StageRS = [fu ∈ FuncUnits |-> {}]
    /\ StageFU = [fu ∈ FuncUnits |-> {}]
    /\ StageCOM = [s ∈ 1..superscalar |-> {}]
    /\ ROB = ⟨⟩
    
Next == 
    /\ NextIF
    /\ NextID
    /\ NextRS
    /\ NextFU
    /\ NextPC

    /\ StageCOM' = [s ∈ 1..superscalar |-> {}]
    /\ ROB' = ⟨⟩

\* NextCOM
\* NextROB

====