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

====