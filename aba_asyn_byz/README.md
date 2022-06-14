# aba_asyn_byz

We verify that `IndInv` is an inductive invariant of the `aba_asyn_byz` model `MC1`

## inductive invariants

To verify that a state predicate `IndInv` is an inductive invariant (i.e. we can use mathematical induction to show that it always holds without having to explore all states), we show two things:

1. *Base case*: All states satisfying the initial state predicate `Init` also satisfy `IndInv`.
2. *Inductive step*: For all states satisfying `IndInv`, all possible next states also satisfy `IndInv`.

Functionally, to verify the base case, we do `apalache check --init=Init --inv=IndInv --length=0 MC1.tla`. This checks that all states resulting from length 0 executions starting from states satisfying `Init` also satisfy `IndInv`. To verify the inductive step, we do `apalache check --init=IndInv --inv=IndInv --length=1 MC1.tla`. This checks that all states resulting from length 1 executions starting from states satisfying `IndInv` also satisfy `IndInv`.
