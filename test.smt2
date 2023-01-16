(declare-sort S 0)

(declare-fun f (S) Int)
(declare-fun c () S)
(declare-fun d () Int)

(assert (>= d (f c)))
(assert (= d 0))

(assert (forall ((X Int))
    (or
        (distinct X 0)
        (forall ((Y S))
            (< X (f Y))))))

(check-sat)