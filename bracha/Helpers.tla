---- MODULE Helpers ----

EXTENDS FiniteSets, Naturals, Sequences, TLC

min[ a, b \in Nat ] == IF a < b THEN a ELSE b

IsPrefix(s, t) ==
    \/  s = <<>>
    \/  \E n \in 1..min[Len(s), Len(t)] : \A i \in 1..n : s[i] = t[i]

ToSet(s) == { s[i] : i \in DOMAIN s }

========================
