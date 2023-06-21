(set-logic HORN)
(declare-fun inv (Int Int Int Int) Bool)

; Initial condition
(assert (forall ((x Int) (m Int) (n Int)) (=> (and (= x 1) (= m 1)) (inv x m n 1))))

; Transition relation
(assert (forall ((x Int) (m Int) (n Int) (x1 Int) (m1 Int) (n1 Int)) (=> (and (inv x m n 1) (< x n) (= x1 (+ x 1)) (= n1 n))
  (or (and (= m1 m) (inv x1 m1 n1 1)) (and (= m1 x) (inv x1 m1 n1 1))))))

; Property
(assert (forall ((x Int) (m Int) (n Int)) (=> (and (inv x m n 1) (not (< x n)) (> n 1)) (>= m 1))))

(check-sat)
(get-model)