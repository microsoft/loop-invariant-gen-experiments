(set-logic HORN)
(declare-fun inv (Int Int Int Int Int) Bool)

; Initial condition
(assert (forall ((a Int) (c Int) (m Int) (j Int) (k Int))
                (=> (and (<= a m) (= j 0) (= k 0))
                    (inv a c m j k))))

; Transition relation
(assert (forall ((a Int) (c Int) (m Int) (j Int) (k Int) (m1 Int) (k1 Int))
                (=> (and (inv a c m j k) (< k c)
                         (ite (< m a) (= m1 a) (= m1 m))
                         (= k1 (+ k 1)))
                    (inv a c m1 j k1))))

; Property
(assert (forall ((a Int) (c Int) (m Int) (j Int) (k Int))
                (=> (and (inv a c m j k) (not (< k c)))
                    (<= a m))))

(check-sat)
(get-model)