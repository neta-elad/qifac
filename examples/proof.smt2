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

(declare-const c1 Int)
(declare-const c2 Int)

(declare-fun P (Int Int) Bool)

; forall-1 :: { (P X Y) } with terms:
;; (P c1 c2)
; produced
;(assert (or (P c1 c2) (P c2 c1)))
; forall-1 :: { (P X Y) } with terms:
;; (P c1 c1)
; produced
(assert (or (P c1 c1) (P c1 c1)))

(assert (not (P c1 c2)))
(assert (not (P c1 c1)))

(check-sat)