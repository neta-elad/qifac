(declare-sort T 0)
(declare-const c T)
(declare-const d T)
(assert (distinct c d))
(check-sat)