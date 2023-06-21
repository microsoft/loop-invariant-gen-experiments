 (set-logic HORN)
     (declare-fun inv (Int Int Int) Bool)
     ; Initial condition
     (assert (forall ((x Int)(y Int)(z Int)) (=> (= x 0) (inv x y z))))
     ; Transition relation
     (assert (forall ((x Int)(y Int)(z Int)(x1 Int)(y1 Int)(z1 Int)) (=> (and (inv x y z) (< x 500) (= x1 (+ x 1)) (ite (<= z y) (= y1 z) (= y1 y)) (= z1 z)) (inv x1 y1 z1))))
     ; Property
     (assert (forall ((x Int)(y Int)(z Int)) (=> (and (inv x y z)(not (< x 500))) (>= z y) )))
     (check-sat)
     (get-model)