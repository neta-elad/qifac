(set-logic ALL)
(declare-sort T 0)
(declare-const c T)
(declare-fun P (T) Bool)
(declare-fun Q (T T) Bool)
(declare-fun f (T) T)
(assert
    (forall ((X T)) (!
        (or
            (P (f X))
            (forall ((Y T)) (!
                (Q X (f Y))
                :qid qQ
                :pattern ((f Y))
            ))
        )
        :qid qP
        :pattern ((f X))
    ))
)
(assert (= (f c) c))
(assert (not (P (f c))))
(assert (= (f (f c)) c))
(assert (not (Q c (f (f c)))))
(check-sat)