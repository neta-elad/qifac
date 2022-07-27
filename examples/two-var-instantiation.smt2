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

(declare-fun c1 () Int)
(declare-fun c2 () Int)

(declare-fun P (Int Int) Bool)

(assert (forall ((X Int) (Y Int)) 
    (! 
		(or 
			(P X Y) 
			(P Y X)
		)
		:qid |forall-1| 
		;:pattern ((f (f X)))
		:pattern ((P X Y))
    )
))


(assert (not (P c1 c2)))
(assert (not (P c1 c1)))

(check-sat)
