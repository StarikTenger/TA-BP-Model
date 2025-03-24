---- MODULE TestBench_TTrace_1742833217 ----
EXTENDS Sequences, TLCExt, TestBench, Toolbox, Naturals, TLC

_expression ==
    LET TestBench_TEExpression == INSTANCE TestBench_TEExpression
    IN TestBench_TEExpression!expression
----

_trace ==
    LET TestBench_TETrace == INSTANCE TestBench_TETrace
    IN TestBench_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        Ready = ({1, 2})
        /\
        StageRS = ([ALU |-> {}, LSU |-> {}])
        /\
        StageFU = ([ALU |-> {}, LSU |-> {}])
        /\
        PC = (7)
        /\
        ROB = (<<>>)
        /\
        StageIF = (<<{}, {}>>)
        /\
        StageID = (<<{}, {6}>>)
        /\
        StageCOM = (<<{1}, {2}>>)
        /\
        ClockCycle = (4)
        /\
        Squashed = ({2, 3, 4, 5})
    )
----

_init ==
    /\ Ready = _TETrace[1].Ready
    /\ Squashed = _TETrace[1].Squashed
    /\ StageRS = _TETrace[1].StageRS
    /\ StageFU = _TETrace[1].StageFU
    /\ ROB = _TETrace[1].ROB
    /\ StageID = _TETrace[1].StageID
    /\ StageIF = _TETrace[1].StageIF
    /\ StageCOM = _TETrace[1].StageCOM
    /\ ClockCycle = _TETrace[1].ClockCycle
    /\ PC = _TETrace[1].PC
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ Ready  = _TETrace[i].Ready
        /\ Ready' = _TETrace[j].Ready
        /\ Squashed  = _TETrace[i].Squashed
        /\ Squashed' = _TETrace[j].Squashed
        /\ StageRS  = _TETrace[i].StageRS
        /\ StageRS' = _TETrace[j].StageRS
        /\ StageFU  = _TETrace[i].StageFU
        /\ StageFU' = _TETrace[j].StageFU
        /\ ROB  = _TETrace[i].ROB
        /\ ROB' = _TETrace[j].ROB
        /\ StageID  = _TETrace[i].StageID
        /\ StageID' = _TETrace[j].StageID
        /\ StageIF  = _TETrace[i].StageIF
        /\ StageIF' = _TETrace[j].StageIF
        /\ StageCOM  = _TETrace[i].StageCOM
        /\ StageCOM' = _TETrace[j].StageCOM
        /\ ClockCycle  = _TETrace[i].ClockCycle
        /\ ClockCycle' = _TETrace[j].ClockCycle
        /\ PC  = _TETrace[i].PC
        /\ PC' = _TETrace[j].PC

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("TestBench_TTrace_1742833217.json", _TETrace)

=============================================================================

 Note that you can extract this module `TestBench_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `TestBench_TEExpression.tla` file takes precedence 
  over the module `TestBench_TEExpression` below).

---- MODULE TestBench_TEExpression ----
EXTENDS Sequences, TLCExt, TestBench, Toolbox, Naturals, TLC

expression == 
    [
        \* To hide variables of the `TestBench` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        Ready |-> Ready
        ,Squashed |-> Squashed
        ,StageRS |-> StageRS
        ,StageFU |-> StageFU
        ,ROB |-> ROB
        ,StageID |-> StageID
        ,StageIF |-> StageIF
        ,StageCOM |-> StageCOM
        ,ClockCycle |-> ClockCycle
        ,PC |-> PC
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_ReadyUnchanged |-> Ready = Ready'
        
        \* Format the `Ready` variable as Json value.
        \* ,_ReadyJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(Ready)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_ReadyModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].Ready # _TETrace[s-1].Ready
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE TestBench_TETrace ----
\*EXTENDS IOUtils, TestBench, TLC
\*
\*trace == IODeserialize("TestBench_TTrace_1742833217.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE TestBench_TETrace ----
EXTENDS TestBench, TLC

trace == 
    <<
    ([Ready |-> {},StageRS |-> [ALU |-> {}, LSU |-> {}],StageFU |-> [ALU |-> {}, LSU |-> {}],PC |-> 0,ROB |-> <<>>,StageIF |-> <<{}, {}>>,StageID |-> <<{}, {}>>,StageCOM |-> <<{}, {}>>,ClockCycle |-> 0,Squashed |-> {}]),
    ([Ready |-> {},StageRS |-> [ALU |-> {}, LSU |-> {}],StageFU |-> [ALU |-> {}, LSU |-> {}],PC |-> 1,ROB |-> <<>>,StageIF |-> <<{[idx |-> 1, cycles_left |-> 1]}, {[idx |-> 2, cycles_left |-> 1]}>>,StageID |-> <<{}, {}>>,StageCOM |-> <<{}, {}>>,ClockCycle |-> 1,Squashed |-> {}]),
    ([Ready |-> {},StageRS |-> [ALU |-> {}, LSU |-> {}],StageFU |-> [ALU |-> {}, LSU |-> {}],PC |-> 3,ROB |-> <<>>,StageIF |-> <<{[idx |-> 3, cycles_left |-> 1]}, {[idx |-> 4, cycles_left |-> 1]}>>,StageID |-> <<{1}, {2}>>,StageCOM |-> <<{}, {}>>,ClockCycle |-> 2,Squashed |-> {}]),
    ([Ready |-> {1, 2},StageRS |-> [ALU |-> {}, LSU |-> {}],StageFU |-> [ALU |-> {[idx |-> 1, cycles_left |-> 1]}, LSU |-> {[idx |-> 2, cycles_left |-> 1]}],PC |-> 5,ROB |-> <<1, 2>>,StageIF |-> <<{[idx |-> 5, cycles_left |-> 1]}, {[idx |-> 6, cycles_left |-> 1]}>>,StageID |-> <<{3}, {4}>>,StageCOM |-> <<{}, {}>>,ClockCycle |-> 3,Squashed |-> {}]),
    ([Ready |-> {1, 2},StageRS |-> [ALU |-> {}, LSU |-> {}],StageFU |-> [ALU |-> {}, LSU |-> {}],PC |-> 7,ROB |-> <<>>,StageIF |-> <<{}, {}>>,StageID |-> <<{}, {6}>>,StageCOM |-> <<{1}, {2}>>,ClockCycle |-> 4,Squashed |-> {2, 3, 4, 5}])
    >>
----


=============================================================================

---- CONFIG TestBench_TTrace_1742833217 ----
CONSTANTS
    prog <- const_prog
    superscalar <- const_superscalar

INVARIANT
    _inv

CHECK_DEADLOCK
    \* CHECK_DEADLOCK off because of PROPERTY or INVARIANT above.
    FALSE

INIT
    _init

NEXT
    _next

CONSTANT
    _TETrace <- _trace

ALIAS
    _expression
=============================================================================
\* Generated on Mon Mar 24 17:20:18 CET 2025