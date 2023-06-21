(set-logic HORN)
(declare-fun inv (Int Int Int Int) Bool)

; Initial condition
(assert (forall ((x Int)(m Int)(n Int)) (=> (and (= x 0) (= m 0)) (inv x m n 0))))

; Transition relation
(assert (forall ((x Int)(m Int)(n Int)(z1 Int)(x1 Int)(m1 Int)(n1 Int)(z2 Int)) (=> (and (inv x m n z1) (< x n) (ite z2 (= m1 x) (= m1 m)) (= x1 (+ x 1)) (= n1 n) (= z2 z2)) (inv x1 m1 n1 z2))))

; Property
(assert (forall ((x Int)(m Int)(n Int)(z1 Int)) (=> (and (inv x m n z1) (not (< x n)) (> n 0)) (>= m 0))))

(check-sat)
(get-model)