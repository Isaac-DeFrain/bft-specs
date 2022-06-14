------------------------- MODULE aba_asyn_byz_typed -------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS
    \* @type: Int;
    N,
    \* @type: Int;
    T,
    \* @type: Int;
    F

VARIABLES
    \* @type: Int;
    nSntE,
    \* @type: Int;
    nSntR,
    \* @typeAlias: PROC = Int;
    \* @type: PROC -> Int;
    nRcvdE,
    \* @type: PROC -> Int;
    nRcvdR,
    \* @type: Int;
    nByz,
    \* @type: PROC -> Str;
    pc
                          

ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0)

Proc == 1 .. N
Location == { "V0", "V1", "EC", "RD", "AC", "BYZ" }
vars == << nSntE, nSntR, nRcvdE, nRcvdR, nByz, pc >>
guardE == (N + T + 2) \div 2
guardR1 == T + 1
guardR2 == 2 * T + 1

Init ==
    /\  nSntE = 0
    /\  nSntR = 0
    /\  nRcvdE = [ i \in Proc |-> 0 ]
    /\  nRcvdR = [ i \in Proc |-> 0 ]
    /\  nByz = 0
    /\  pc \in [ Proc -> { "V0", "V1" } ]

BecomeByzantine(i) ==
    /\  nByz < F
    /\  nByz' = nByz + 1  
    /\  pc' = [ pc EXCEPT ![i] = "BYZ" ]  
    /\  UNCHANGED << nSntE, nSntR, nRcvdE, nRcvdR >>

Receive(i, includeByz) ==
    \/  /\  nRcvdE[i] < nSntE + (IF includeByz THEN nByz ELSE 0)
        /\  nRcvdE' = [ nRcvdE EXCEPT ![i] = nRcvdE[i] + 1 ]
        /\  UNCHANGED << nSntE, nSntR, nRcvdR, nByz, pc >>
    \/  /\  nRcvdR[i] < nSntR + (IF includeByz THEN nByz ELSE 0)
        /\  nRcvdR' = [ nRcvdR EXCEPT ![i] = nRcvdR[i] + 1 ]
        /\  UNCHANGED << nSntE, nSntR, nRcvdE, nByz, pc >>

SendEcho(i) ==
    /\  \/ pc[i] = "V1"
        \/  /\ pc[i] = "V0"
            /\  \/ nRcvdE[i] >= guardE
                \/ nRcvdR[i] >= guardR1
    /\  pc' = [ pc EXCEPT ![i] = "EC" ]
    /\  nSntE' = nSntE + 1
    /\  UNCHANGED << nSntR, nRcvdE, nRcvdR, nByz >>

SendReady(i) ==
    /\  pc[i] = "EC" 
    /\  \/  nRcvdE[i] >= guardE
        \/  nRcvdR[i] >= guardR1
    /\  pc' = [ pc EXCEPT ![i] = "RD" ]
    /\  nSntR' = nSntR + 1
    /\  UNCHANGED << nSntE, nRcvdE, nRcvdR, nByz >>

Decide(i) ==
    /\  pc[i] = "RD"     
    /\  nRcvdR[i] >= guardR2
    /\  pc' = [ pc EXCEPT ![i] = "AC" ]
    /\  UNCHANGED << nSntE, nSntR, nRcvdE, nRcvdR, nByz >>

Next == \E self \in Proc :
    \/  BecomeByzantine(self)
    \/  Receive(self, TRUE)
    \/  SendEcho(self)
    \/  SendReady(self)
    \/  Decide(self)
    \/  UNCHANGED vars

Spec == Init /\ [][Next]_vars

FairSpec ==
    /\  Spec
    /\  WF_vars(\E self \in Proc :
            \/  Receive(self, FALSE)
            \/  SendEcho(self)
            \/  SendReady(self)
            \/  Decide(self)
        )

TypeOK == 
    /\  pc \in [ Proc -> Location ]          
    /\  nSntE \in 0..N
    /\  nSntR \in 0..N
    /\  nByz \in 0..F
    /\  nRcvdE \in [ Proc -> 0..(N + F) ]
    /\  nRcvdR \in [ Proc -> 0..(N + F) ]

Unforg_Ltl ==
    (\A i \in Proc : pc[i] = "V0") => [](\A i \in Proc : pc[i] # "AC")

Corr_Ltl ==
    (\A i \in Proc : pc[i] = "V1") => <>( \E i \in Proc : pc[i] = "AC" )

Agreement_Ltl ==
    []((\E i \in Proc : pc[i] = "AC") => <>(\A i \in Proc : pc[i] = "AC" \/ pc[i] = "BYZ" ))

----

\* inductive invariant
IndInv ==
    /\  TypeOK
    /\  nSntE <= Cardinality({ i \in Proc : pc[i] \in { "EC", "RD", "AC", "BYZ" } })
    /\  nSntR <= Cardinality({ i \in Proc : pc[i] \in { "RD", "AC", "BYZ" } })
    /\  nByz = Cardinality({ i \in Proc : pc[i] = "BYZ" })

=============================================================================
