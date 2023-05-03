 (set-logic HORN)
     (declare-fun inv (Int Int Int Int) Bool)
     ; Initial condition
     (assert (forall ((i Int)(j Int)(x Int)(y Int)) (=> ( and (= i x) (= j y)) (inv i j x y))))
     ; Transition relation
     (assert (forall ((i Int)(j Int)(x Int)(y Int)(x1 Int)(y1 Int)) (=> (and (inv i j x y) (not (= x 0)) (= x1 (- x 1)) (= y1 (- y 1)) ) (inv i j x1 y1))))
     ; Property
     (assert (forall ((i Int)(j Int)(x Int)(y Int)) (=> (and (inv i j x y)(= x 0) (= i j)) (= y 0) )))
     (check-sat)
     (get-model)