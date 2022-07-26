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


(declare-const c Int)
(declare-const d Int)
(declare-fun P (Int) Bool)
(declare-fun R (Int Int) Bool)

(declare-const |Q-outer| Bool)
(declare-const |Q-inner1| Bool)
(declare-const |Q-inner2| Bool)

(assert |Q-outer|)

;(assert (! (or (not |Q-outer|) (or (P d) |Q-inner1|)) :named |outer, (P d)|))
(assert (! (or (not |Q-outer|) (or (P c) |Q-inner2|)) :named |outer, (P c)|))
(assert (! (or (not |Q-inner2|) (R c c)) :named |inner, (R c c), c == c|))

(assert (not (P d)))
(assert (not (P c)))
(assert (not (R c c)))

(check-sat)
