---- MODULE Helpers ----

EXTENDS FiniteSets, Integers, Naturals, Sequences, TLC

max[ a, b \in Int ] == IF a > b THEN a ELSE b

Max(S) == CHOOSE x \in S : \A y \in S : x >= y

========================
