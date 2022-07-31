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
;(set-option :produce-proofs true)
(set-info :category "industrial")

(declare-fun c () Int)
(declare-fun P (Int Int) Bool)
;(declare-fun Z!0 (Int) Int)

;(assert (< (Z!0 c) c))

(assert (forall ((X Int) (Y Int)) (!
    (P X Y)
    :qid q1
    :pattern ((P X Y))
)))

(assert (forall ((W Int)) (!
    (not (forall ((Z Int)) (!
        (not (P W Z))
        :qid q3
    )))
    :qid q2
    :pattern ((P W W))
)))

(assert (forall ((W Int)) (!
    (exists ((Z Int)) (!
        (not (P W Z))
        :qid q5
    ))
    :qid q4
    :pattern ((P W W))
)))

(assert (P 0 0))

(check-sat)
;(get-proof)