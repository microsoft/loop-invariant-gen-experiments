 (set-logic HORN)
     (declare-fun inv (Int Int) Bool)
     ; Initial condition
     (assert (forall ((x Int)(y Int)) (=> ( and (= x 1) (= y 0)) (inv x y))))
     ; Transition relation
     (assert (forall ((x Int)(y Int)(x1 Int)(y1 Int)) (=> (and (inv x y) (< y 1000) (= x1 (+ x y)) (= y1 (+ y 1)) ) (inv x1 y1))))
     ; Property
     (assert (forall ((x Int)(y Int)) (=> (and (inv x y)(not (< y 1000))) (>= x y) )))
     (check-sat)
     (get-model)