(declare-sort Node 0)
(declare-sort Quorum 0)
(declare-sort Value 0)

(declare-fun member (Node Quorum) Bool)
(declare-fun intersection (Quorum Quorum) Node)
(declare-fun vote (Node Value) Bool)
(declare-fun decided (Value) Bool)
(declare-fun quorum-of-decided (Value) Quorum)

(declare-fun v1 () Value)
(declare-fun v2 () Value)
(declare-fun q2 () Quorum)

(assert (decided v1))
(assert (distinct v1 v2))

(assert (forall ((Q1 Quorum) (Q2 Quorum))
    (member (intersection Q1 Q2) Q1)
))

(assert (forall ((Q1 Quorum) (Q2 Quorum))
    (member (intersection Q1 Q2) Q2)
))

(assert (forall ((N Node) (V1 Value) (V2 Value))
    (=>
        (and
            (vote N V1)
            (vote N V2)
        )
        (= V1 V2)
    )
))

(assert (forall ((V Value) (N Node))
    (=>
        (decided V)
        (=>
            (member N (quorum-of-decided V))
            (vote N V)
        )
    )
))

(assert (forall ((N Node))
    (=>
        (member N q2)
        (vote N v2)
    )
))
