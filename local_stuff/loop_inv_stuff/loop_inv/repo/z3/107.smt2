 (set-logic HORN)
     (declare-fun inv (Int Int Int Int) Bool)
     ; Initial condition
     (assert (forall ((a Int)(m Int)(j Int)(k Int)) (=> (and (= j 0) (= k 0)) (inv a m j k))))
     ; Transition relation
     (assert (forall ((a Int)(m Int)(j Int)(k Int)(a1 Int)(m1 Int)(j1 Int)(k1 Int)) (=> (and (inv a m j k) (< k 1) (ite (< m a) (= m1 a) (= m1 m)) (= a1 a) (= j1 j) (= k1 (+ k 1))) (inv a1 m1 j1 k1))))
     ; Property
     (assert (forall ((a Int)(m Int)(j Int)(k Int)) (=> (and (inv a m j k)(not (< k 1))) (<= a m))))
     (check-sat)
     (get-model)