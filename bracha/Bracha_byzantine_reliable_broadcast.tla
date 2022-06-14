---- MODULE Bracha_byzantine_reliable_broadcast ----

EXTENDS Helpers

CONSTANTS
    Faulty,     \* set of faulty process ids
    Correct,    \* set of correct process ids
    Value       \* the values each process can propose/accept
                \* e.g. (p, v) for mulitple instances initialized by p
                \* e.g. (p, k, v) for multiple instances and rounds

VARIABLES
    origin,     \* broadcasting process
    net,        \* reliable point-to-point network; net[sndr, rcvr]
    pc,         \* control state of each process
    rcvdMsgs,   \* each process has a set of received messages
    value       \* the value decided by each process

vars == <<origin, net, pc, rcvdMsgs, value>>

Proc == Correct \cup Faulty
N == Cardinality(Proc)
F == Cardinality(Faulty)

\* threshold of faulty processes
T == (N - 1) \div 3

ASSUME F <= T

----------------------------------------------------

\* helpers

ControlStates == { "Init", "Echo", "Ready", "Accept", "Deliver" }

\* messages
InitMsg  == [ type : {"init"},  sndr : Proc, value : Value ]
EchoMsg  == [ type : {"echo"},  sndr : Proc, value : Value ]
ReadyMsg == [ type : {"ready"}, sndr : Proc, value : Value ]
Msg == InitMsg \cup EchoMsg \cup ReadyMsg

\* message constructors
init_msg(p, v)  == [ type |-> "init",  sndr |-> p, value |-> v ]
echo_msg(p, v)  == [ type |-> "echo",  sndr |-> p, value |-> v ]
ready_msg(p, v) == [ type |-> "ready", sndr |-> p, value |-> v ]

\* message sets
init_msgs(p, v)  == { m \in rcvdMsgs[p] : m.type = "init"  /\ m.value = v }
echo_msgs(p, v)  == { m \in rcvdMsgs[p] : m.type = "echo"  /\ m.value = v }
ready_msgs(p, v) == { m \in rcvdMsgs[p] : m.type = "ready" /\ m.value = v }

sent_msgs(p) == ToSet(net[p, p]) \cup { m \in rcvdMsgs[p] : m.sndr = p }

\* action guards = enabling conditions
echo_guard(p, v) ==
    \/  init_msgs(p, v) # {}
    \/  Cardinality(echo_msgs(p, v)) >= (N + T) \div 2
    \/  Cardinality(ready_msgs(p, v)) >= T + 1

ready_guard(p, v) ==
    \/  Cardinality(echo_msgs(p, v)) >= (N + T) \div 2
    \/  Cardinality(ready_msgs(p, v)) >= T + 1

accept_guard(p, v) == Cardinality(ready_msgs(p, v)) >= 2 * T + 1

----------------------------------------------------

\* a correct process [p] sends [msg] to all processes
\* a faulty process [p] either sends:
\* - [msg] to all processes, or
\* - a message with a different value to all processes
\* note: only echo and ready messages are sent via Send
Send(p, msg) ==
    \/  /\  p \in Correct
        /\  net' = [ s \in {p}, r \in Proc |-> Append(net[p, r], msg) ] @@ net
    \/  /\  p \in Faulty
            \*  faulty proc sends correct message
        /\  \/  net' = [ s \in {p}, r \in Proc |-> Append(net[s, r], msg) ] @@ net
            \*  faulty proc send faulty message
            \/  \E u \in Value \ {msg.value} :
                    net' = [ s \in {p}, r \in Proc |->
                        Append(net[s, r], [ msg EXCEPT !.value = u ]) ]

----------------------------------------------------

\* next actions

\* [origin] broadcasts (initial, v)
\* note: correct and faulty processes initialize the ame way
Initialize(p, v) ==
    LET msg == init_msg(p, v) IN
    /\  p = origin
    /\  pc[p] = "Init"
    /\  pc' = [ pc EXCEPT ![p] = "Echo" ]
    /\  net' = [ s \in {p}, r \in Proc |-> Append(net[p, r], msg) ] @@ net
    /\  UNCHANGED <<origin, rcvdMsgs, value>>

\* if [p] has been sent any messages, they receive all of them
Receive(p) ==
    LET msgs == UNION { ToSet(net[s, p]) : s \in Proc } IN
    /\  msgs # {}
    /\  net' = [ s \in Proc, r \in {p} |-> <<>> ] @@ net
    /\  rcvdMsgs' = [ rcvdMsgs EXCEPT ![p] = @ \cup msgs ]
    /\  UNCHANGED <<origin, pc, value>>

\* [p] waits until receipt of
\* - one (initial, v) message
\* - (N + T) / 2 (echo, v) messages
\* - (T + 1) (ready, v) messages
\* then broadcasts (echo, v)
\* note: (N + T) / 2 < 2N / 3
Echo(p, v) ==
    /\  pc[p] = "Echo"
    /\  echo_guard(p, v)
    /\  Send(p, echo_msg(p, v))
    /\  pc' = [ pc EXCEPT ![p] = "Ready" ]
    /\  UNCHANGED <<origin, rcvdMsgs, value>>

\* [p] waits until receipt of
\* - (N + T) / 2 (echo, v) messages
\* - (T + 1) (ready, v) messages
\* then broadcasts (ready, v)
Ready(p, v) ==
    /\  pc[p] = "Ready"
    /\  ready_guard(p, v)
    /\  Send(p, ready_msg(p, v))
    /\  pc' = [ pc EXCEPT ![p] = "Accept" ]
    /\  UNCHANGED <<origin, rcvdMsgs, value>>

\* [p] waits until receipt of (2T + 1) (ready, v) messages
\* then accepts [v]
Accept(p, v) ==
    /\  pc[p] = "Accept"
    /\  accept_guard(p, v)
    /\  pc' = [ pc EXCEPT ![p] = "Deliver" ]
    /\  value' = [ value EXCEPT ![p] = Append(@, v) ]
    /\  UNCHANGED <<origin, net, rcvdMsgs>>

----------------------------------------------------

\* brb-broadcast\deliver specification

Init == \E op \in Proc :
    /\  origin   = op
    /\  net      = [ s \in Proc, r \in Proc |-> <<>> ]
    /\  pc       = [ p \in Proc |-> IF p = op THEN "Init" ELSE "Echo" ]
    /\  rcvdMsgs = [ p \in Proc |-> {} ]
    /\  value    = [ p \in Proc |-> <<>> ]

Next == \E p \in Proc, v \in Value :
    \/  Initialize(p, v)
    \/  Receive(p)
    \/  Echo(p, v)
    \/  Ready(p, v)
    \/  Accept(p, v)

Spec == Init /\ [][Next]_vars

----------------------------------------------------

\* invariants & safety

TypeOK ==
    /\  origin   \in Proc
    /\  net      \in [ Proc \X Proc -> Seq(Msg) ]
    /\  pc       \in [ Proc -> ControlStates ]
    /\  rcvdMsgs \in [ Proc -> SUBSET Msg ]
    /\  value    \in [ Proc -> Seq(Value) ]

\* Lemma 1
\* correct procesess send at most one ready message and
\* if two correct processes send a ready message, it is for the same value
ReadySendConsistency == \A p, q \in Correct :
    LET ready(pp) == { m.value : m \in { mm \in sent_msgs(pp) : mm.type = "ready" } } IN
    /\  Cardinality(ready(p)) <= 1
    /\  Cardinality(ready(q)) <= 1
    /\  \/  ready(p) = {}
        \/  ready(q) = {}
        \/  ready(p) = ready(q)

\* Lemma 2
DeliverConsistency == \A p, q \in Correct :
    \/  IsPrefix(value[p], value[q])
    \/  IsPrefix(value[q], value[p])

\* a correct process brb-delivers at most one value
Integrity == \A p \in Correct : Len(value[p]) <= 1

\* since this spec only addresses a single brb instance, there will be deadlocks
AcceptableDeadlock ==
    ~ ENABLED Next =>
        \/  /\  origin \in Faulty
            /\  \/  \E v \in Value : \A p \in Correct : value[p] = <<v>>
                \/  \A p \in Correct : value[p] = <<>>
        \/  /\  origin \in Correct
            /\  \E v \in Value : \A p \in Correct : value[p] = <<v>>

THEOREM Spec =>
    /\  TypeOK
    /\  Integrity
    /\  DeliverConsistency
    /\  AcceptableDeadlock
    /\  ReadySendConsistency

----------------------------------------------------

\* fairness & liveness

\* only correct processes must do the actions
\* faulty processes can fail-stop
Fairness == WF_vars(\E p \in Correct, v \in Value :
    \/  Initialize(p, v)
    \/  Receive(p)
    \/  Echo(p, v)
    \/  Ready(p, v)
    \/  Accept(p, v) 
)

FairSpec == Spec /\ Fairness

\* Lemma 3
\* if a correct process brb-delivers a message m, then all correct processes brb-deliver m
CorrectDeliverTermination == \A v \in Value :
    (\E p \in Correct : value[p] = <<v>>) ~> (\A p \in Correct : value[p] = <<v>>)

\* Lemma 4
\* if a correct process brb-broadcasts a message m, then all correct processes brb-deliver m 
CorrectBroadcastTermination == \A v \in Value :
    LET initMsgs == { m \in sent_msgs(origin) : m.type = "init" } IN
    (origin \in Correct /\ v \in { m.value : m \in initMsgs }) ~>
        (\A p \in Correct : value[p] = <<v>>)

Termination ==
    /\  CorrectDeliverTermination
    /\  CorrectBroadcastTermination

\* if a faulty process brb-braodcasts a message m, then either:
\* - all correct processes brb-deliver m
\* - no correct process brb-delivers m
FaultyBroadcastTermination == \A v \in Value :
    LET initMsgs == { m \in sent_msgs(origin) : m.type = "init" } IN
    (origin \in Faulty /\ v \in { m.value : m \in initMsgs }) ~> (
            \/  \A p \in Correct : value[p] = <<v>>
            \/  \A p \in Correct : value[p] = <<>>
        )

\* Theorem 1
THEOREM FairSpec =>
    /\  Termination
    /\  FaultyBroadcastTermination

====================================================
