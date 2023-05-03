 (set-logic HORN)
     (declare-fun inv (Int Int Int) Bool)
     ; Initial condition
     (assert (forall ((i Int)(x Int)(y Int)) (=> (and (= i 0) (>= x 0) (>= y 0) (>= x y)) (inv i x y))))
     ; Transition relation
     (assert (forall ((i Int)(x Int)(y Int)(i1 Int)(x1 Int)(y1 Int)) (=> (and (inv i x y) (ite (< i y) (= i1 (+ i 1)) (= i1 i)) (= x1 x) (= y1 y)) (inv i1 x1 y1))))
     ; Property
     (assert (forall ((i Int)(x Int)(y Int)) (=> (and (inv i x y) (>= i x) (< 0 i)) (>= i y))))
     (check-sat)
     (get-model)