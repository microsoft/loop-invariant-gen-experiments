(set-logic HORN)
(declare-fun inv (Int Int Int Int Int) Bool)

; Initial condition
(assert (forall ((a Int) (c Int) (m Int) (j Int) (k Int))
                (=> (and (= j 0) (= k 0))
                    (inv a c m j k))))

; Transition relation
(assert (forall ((a Int) (c Int) (m Int) (j Int) (k Int) (m1 Int) (k1 Int))
                (=> (and (inv a c m j k) (< k c))
                    (or (and (= m1 (ite (< m a) a m)) (= k1 (+ k 1)) (inv a c m1 j k1))
                        (and (= m1 m) (= k1 (+ k 1)) (inv a c m1 j k1))))))

; Property
(assert (forall ((a Int) (c Int) (m Int) (j Int) (k Int))
                (=> (and (inv a c m j k) (not (< k c)) (> c 0))
                    (<= a m))))

(check-sat)
(get-model)