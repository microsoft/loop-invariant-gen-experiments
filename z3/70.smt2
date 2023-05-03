 (set-logic HORN)
     (declare-fun inv (Int Int Int) Bool)
     ; Initial condition
     (assert (forall ((n Int)(x Int)(y Int)) (=> (and (= x 1)) (inv n x y))))
     ; Transition relation
     (assert (forall ((n Int)(x Int)(y Int)(x1 Int)(y1 Int)) (=> (and (inv n x y) (<= x n) (= y (- n x)) (= x1 (+ x 1))) (inv n x1 y1))))
     ; Property
     (assert (forall ((n Int)(x Int)(y Int)) (=> (and (inv n x y)(not (<= x n)) (> n 0)) (< y n))))
     (check-sat)
     (get-model)