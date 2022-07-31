(set-option :smt.qi.profile true)
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

(declare-fun f (Int) Int)
;(declare-const c Int)
(declare-fun P (Int Int) Bool)
(declare-fun c () Int)

(assert (P c c))

(assert (forall ((X Int)) 
    (! 
		(P (f X) X) 
		:qid |forall-1| 
		;:pattern ((f (f X)))
		:pattern ((f X))
    )
))

;(assert (forall ((X Int))
;	(!
;		(P X X)
;		:qid |forall-2|
;		:pattern ((P X X))
;	)
;))
;
;(assert (P (f c) (f c)))
;(assert (P (f (f c)) (f c)))
;(assert (P (f (f (f c))) (f (f c))))

(assert 
	(exists ((X Int))
		(not (P (f X) X))
	)
)

; (assert (not (P (f c) c)))


(check-sat)
