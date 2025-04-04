---- MODULE Util ----
EXTENDS TLC, Integers, Sequences, FiniteSets, FiniteSetsExt

Positive == Nat \ {0}

Decrement(x) ==
    IF x = 1 THEN 1 ELSE x - 1

\* Helper functions for Option ({x} or {})

Unwrap(X) ==
    CHOOSE x ∈ X : TRUE

AllInSeq(seq) ==
    UNION {seq[i] : i ∈ 1..Len(seq)}

DropHead(seq, n) ==
    [i ∈ 1..(Len(seq) - n) |-> seq[i + n]]

RECURSIVE Erase(_,_)

Erase(seq, set) ==
    IF seq = ⟨⟩
    THEN ⟨⟩
    ELSE (IF Head(seq) ∉ set THEN ⟨Head(seq)⟩ ELSE ⟨⟩) ∘ Erase(Tail(seq), set)

\* ⟨{1}, {2}, {}, {3}⟩ -> ⟨1,2,3⟩
RECURSIVE FlattenSeq(_)
FlattenSeq(seq) ==
    IF seq = ⟨⟩ THEN ⟨⟩ ELSE 
    (IF Head(seq) = {} THEN ⟨⟩ ELSE
    ⟨Unwrap(Head(seq))⟩) ∘ FlattenSeq(Tail(seq))

RECURSIVE __CartProd(_)
__CartProd(seq) == 
    IF Len(seq) = 1 THEN {⟨entry⟩ : entry ∈ seq[1]} ELSE Head(seq) × __CartProd(Tail(seq))

RECURSIVE Flatten(_)
Flatten(seq) == 
    IF Len(seq) = 1 THEN ⟨seq[1]⟩ ELSE ⟨seq[1]⟩ ∘ Flatten(Tail(seq)[1])

CartProd(seq) == {Flatten(entry) : entry ∈ __CartProd(seq)}

====