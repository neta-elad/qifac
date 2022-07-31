(set-info :smt-lib-version 2.6)
(set-option :auto_config false)
(set-option :type_check true)
(set-option :smt.case_split 3)
(set-option :smt.qi.eager_threshold 100)
(set-option :smt.delay_units true)
(set-option :smt.arith.solver 2)
(set-option :smt.arith.nl false)
(set-option :smt.mbqi false)
(set-option :model.compact false)
(set-option :model.v2 true)
(set-option :pp.bv_literals false)
(set-info :category "industrial")

(declare-fun c () Int)
(declare-fun f (Int) Int)
(declare-fun P (Int Int Int) Bool)

(assert (forall ((X Int) (Y Int) (Z Int)) (!
    (P X Y Z)
    :qid q1
    :pattern ((P X Y Z))
)))

(assert (forall ((W Int)) (!
    (exists ((|a#1#0#0@@8| Int)) (!
        (and 
            (forall ((T Int)) (!
                (not (P W |a#1#0#0@@8| T))
                :qid q4
                :pattern ((P W |a#1#0#0@@8| T))
            ))
            (= W |a#1#0#0@@8|)
        )
        :qid q3
    ))
    :qid q2
    :pattern ((P W W W))
)))

(assert (P c c c))
(assert (P (f c) (f c) (f c)))

; ***

;(assert (! 
;    (or 
;        (not (forall ((W Int)) (! 
;            (not (or 
;                (not (forall ((T Int)) (! 
;                    (not (P W (|a#1#0#0@@8!0| W) T)) 
;                    :qid q4 
;                    :pattern ((P W (|a#1#0#0@@8!0| W) T))
;                ))) 
;                (not (= W (|a#1#0#0@@8!0| W)))
;            )) 
;            :qid q2 
;            :pattern ((P W W W)))
;        )) 
;        (not (or 
;            (not (forall ((T Int)) (! 
;                (not (P c (|a#1#0#0@@8!0| c) T)) 
;                :qid q4 
;                :pattern ((P c (|a#1#0#0@@8!0| c) T))
;            ))) 
;            (not (= c (|a#1#0#0@@8!0| c)))
;        ))
;    ) 
;    :named |NN0q2, (P c c c), c == c, c == c, c == c, c == c|
;))

;(assert (! 
;    (or 
;        (not (forall ((T Int)) (! 
;            (not (P c (|a#1#0#0@@8!0| c) T)) 
;            :qid q4 
;            :pattern ((P c (|a#1#0#0@@8!0| c) T)))
;        )) 
;        (not (P c (|a#1#0#0@@8!0| c) (|a#1#0#0@@8!0| c)))
;    ) 
;    :named |NN1q4, (P c c c), c == c, c == (a#1#0#0@@8!0 c)|
;))

(check-sat)