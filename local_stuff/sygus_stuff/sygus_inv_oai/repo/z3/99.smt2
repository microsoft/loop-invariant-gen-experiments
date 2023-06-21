(set-logic HORN)
(declare-fun inv (Int Int Int) Bool)

; Initial condition
(assert (forall ((n Int)(x Int)(y Int)) (=> (and (>= n 0) (= x n) (= y 0)) (inv n x y))))

; Transition relation
(assert (forall ((n Int)(x Int)(y Int)(x1 Int)(y1 Int)) (=> (and (inv n x y) (> x 0) (= y1 (+ y 1)) (= x1 (- x 1))) (inv n x1 y1))))

; Property
(assert (forall ((n Int)(x Int)(y Int)) (=> (and (inv n x y) (<= x 0)) (= n (+ x y)))))

(check-sat)
(get-model)