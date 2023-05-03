 (set-logic HORN)
     (declare-fun inv (Int Int) Bool)
     ; Initial condition
     (assert (forall ((x Int)(y Int)) (=> ( and (= x 1)) (inv x y))))
     ; Transition relation
     (assert (forall ((x Int)(y Int)(x1 Int)(y1 Int)) (=> (and (inv x y) (< x y) (= x1 (+ x x)) (= y1 y) ) (inv x1 y1))))
     ; Property
     (assert (forall ((x Int)(y Int)) (=> (and (inv x y)(not (< x y))) (>= x 1) )))
     (check-sat)
     (get-model)