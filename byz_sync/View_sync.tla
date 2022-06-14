---- MODULE View_sync ----

EXTENDS Helpers

CONSTANTS
    Correct,
    Faulty,
    View

VARIABLES
    max_views,  \* each process track the highest view wished by each peer
    net,        \* authenticated, point-to-point network
    rcvd_msgs,  \* TODO
    send_view,  \* TODO
    timer_view, \* TODO
    view,       \* each process maintains their current view
    _view       \* TODO

vars == <<max_views, net, rcvd_msgs, send_view, timer_view, view, _view>>

Proc == Correct \cup Faulty

--------------------------

Msg == [ sndr : Proc, wish : View ]

--------------------------

\* next actions

Start(p) ==
    /\  _view[p] = 0
    /\  net' = [ s \in {p}, r \in Proc |-> Append(net[s, r], [ wish |-> 1 ]) ] @@ net
    /\  UNCHANGED <<max_views, rcvd_msgs, send_view, timer_view, view, _view>>

==========================
