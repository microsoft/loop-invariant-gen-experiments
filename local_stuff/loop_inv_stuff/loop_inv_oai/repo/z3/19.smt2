(set-logic HORN)
(declare-fun inv (Int Int Int Int) Bool)

; Initial condition
(assert (forall ((x Int)(m Int)(n Int)(z1 Int)) (=> (and (= x 0) (= m 0)) (inv x m n z1))))

; Transition relation
(assert (forall ((x Int)(m Int)(n Int)(z1 Int)(x1 Int)(m1 Int)(z2 Int)) (=> (and (inv x m n z1) (< x n) (ite z2 (= m1 x) (= m1 m)) (= x1 (+ x 1))) (inv x1 m1 n z2))))

; Property
(assert (forall ((x Int)(m Int)(n Int)(z1 Int)) (=> (and (inv x m n z1) (not (< x n)) (> n 0)) (< m n))))

(check-sat)
(get-model)

; The second assertion (m >= 0) is trivially true, as m is always assigned a value between 0 and n-1.