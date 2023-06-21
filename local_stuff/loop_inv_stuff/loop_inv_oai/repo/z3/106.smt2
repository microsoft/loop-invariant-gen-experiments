(set-logic HORN)
(declare-fun inv (Int Int Int Int) Bool)

; Initial condition
(assert (forall ((a Int) (m Int) (j Int) (k Int))
                (=> (and (<= a m) (< j 1) (= k 0))
                    (inv a m j k))))

; Transition relation
(assert (forall ((a Int) (m Int) (j Int) (k Int) (m1 Int) (k1 Int))
                (=> (and (inv a m j k) (< k 1)
                         (ite (< m a) (= m1 a) (= m1 m))
                         (= k1 (+ k 1)))
                    (inv a m1 j k1))))

; Property
(assert (forall ((a Int) (m Int) (j Int) (k Int))
                (=> (and (inv a m j k) (not (< k 1)))
                    (>= a m))))

(check-sat)
(get-model)