---- MODULE Synchronizer ----

EXTENDS Helpers

CONSTANT
    F,
    p,
    Proc,
    View

VARIABLES
    max_views,
    rcvd_msgs,
    send_msgs,
    send_view,
    timer_view,
    view,
    _view

vars == <<max_views, rcvd_msgs, send_msgs, send_view, timer_view, view, _view>>

ASSUME p \in Proc

-----------------------------

LOCAL Msg == [ sndr : Proc, wish : View ]
LOCAL wish(v) == [ sndr |-> p, wish |-> v ]

-----------------------------

TypeOK ==
    /\  max_views  \in [ Proc -> View ]
    /\  rcvd_msgs  \in Seq(Msg)
    /\  send_msgs  \in Seq(Msg)
    /\  send_view  \in BOOLEAN
    /\  timer_view \in BOOLEAN
    /\  view       \in View
    /\  _view      \in View

-----------------------------

Start ==
    /\  _view = 0
    /\  send_msgs' = Append(send_msgs, wish(1))
    /\  UNCHANGED <<max_views, timer_view, view, _view>>

Timeout ==
    LET msg == wish(max[view + 1, _view]) IN
    /\  timer_view
    /\  timer_view' = FALSE
    /\  send_msgs' = Append(send_msgs, msg)
    /\  UNCHANGED <<max_views, view, _view>>

Periodically ==
    /\  ~send_view
    /\  \/  /\  timer_view
            /\  send_msgs' = Append(send_msgs, wish(_view))
        \/  /\  ~timer_view
            /\  \/  /\  max_views[p] > 0
                    /\  send_msgs' = Append(send_msgs, wish(max[view + 1, _view]))
                \/  UNCHANGED send_msgs
    /\  UNCHANGED <<max_views, rcvd_msgs, timer_view, view, _view>>

Receive(msg) ==
    /\  rcvd_msgs' = Append(rcvd_msgs, msg)
    /\  UNCHANGED <<max_views, send_msgs, timer_view, view, _view>>

ParseWish ==
    /\  rcvd_msgs # <<>>
    /\  LET msg == Head(rcvd_msgs)
            q == msg.sndr
            v == msg.wish
        IN
        /\  rcvd_msgs' = Tail(rcvd_msgs)
        /\  \/  /\  v > max_views[q]
                /\  max_views' = [ max_views EXCEPT ![q] = v ]
            \/  UNCHANGED max_views
        /\  view' = Max({ vv \in View : \E r \in Proc :
                            /\  max_views[r] = vv
                            /\  Cardinality({ s \in Proc : max_views[s] >= vv }) >= 2 * F + 1
                    })
        /\  _view' = Max({ vv \in View : \E r \in Proc :
                            /\  max_views[r] = vv
                            /\  Cardinality({ s \in Proc : max_views[s] >= vv }) >= F + 1
                    })
        /\  \/  /\  _view' = view'
                /\  view' > view
                /\  timer_view' = TRUE
            \/  UNCHANGED timer_view
        /\  \/  /\  _view' > _view
                /\  send_msgs' = Append(send_msgs, wish(_view'))
            \/  UNCHANGED send_msgs

-----------------------------

Init  ==
    /\  max_views  = [ q \in Proc |-> 0 ]
    /\  rcvd_msgs  = <<>>
    /\  send_msgs  = <<>>
    /\  timer_view = TRUE
    /\  view       = 0
    /\  _view      = 0

Next ==
    \/  Start
    \/  Timeout
    \/  Periodically
    \/  \E m \in Msg : Receive(m)
    \/  ParseWish

=============================
