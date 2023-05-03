 (set-logic HORN)
     (declare-fun inv (Int Int Int) Bool)
     ; Initial condition
     (assert (forall ((n Int)(y Int)(x Int)) (=> (and (= x 1)) (inv n y x))))
     ; Transition relation
     (assert (forall ((n Int)(y Int)(x Int)(y1 Int)(x1 Int)) (=> (and (inv n y x) (<= x n) (= y1 (- n x)) (= x1 (+ x 1)) ) (inv n y1 x1))))
     ; Property
     (assert (forall ((n Int)(y Int)(x Int)) (=> (and (inv n y x)(not (<= x n)) (> n 0)) (>= y 0) )))
     (check-sat)
     (get-model)