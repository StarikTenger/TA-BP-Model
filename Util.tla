---- MODULE Util ----
EXTENDS TLC, Integers, Sequences, FiniteSets

Positive == Nat \ {0}

Decrement(x) ==
    IF x = 1 THEN 1 ELSE x - 1

\* Helper functions for Option ({x} or {})

Unwrap(X) ==
    CHOOSE x ∈ X : TRUE

AllInSeq(seq) ==
    UNION {seq[i] : i ∈ 1..Len(seq)}

Max(set) ==
    CHOOSE x ∈ set : ∀ x1 ∈ set : x >= x1

Min(set) ==
    CHOOSE x ∈ set : ∀ x1 ∈ set : x <= x1

DropHead(seq, n) ==
    [i ∈ 1..(Len(seq) - n) |-> seq[i + n]]

RECURSIVE Erase(_,_)

Erase(seq, set) ==
    IF seq = ⟨⟩
    THEN ⟨⟩
    ELSE (IF Head(seq) ∉ set THEN ⟨Head(seq)⟩ ELSE ⟨⟩) ∘ Erase(Tail(seq), set)


RECURSIVE FlattenSeq(_)
FlattenSeq(seq) ==
    IF seq = ⟨⟩ THEN ⟨⟩ ELSE 
    (IF Head(seq) = {} THEN ⟨⟩ ELSE
    ⟨Unwrap(Head(seq))⟩) ∘ FlattenSeq(Tail(seq))

====