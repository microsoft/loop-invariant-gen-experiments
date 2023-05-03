 (set-logic HORN)
     (declare-fun inv (Int Int Int Int Int Int) Bool)
     ; Initial condition
     (assert (forall ((lock Int)(v1 Int)(v2 Int)(v3 Int)(x Int)(y Int)) (=> ( and (= x y) (= lock 1)) (inv lock v1 v2 v3 x y))))
     ; Transition relation
     (assert (forall ((lock Int)(v1 Int)(v2 Int)(v3 Int)(x Int)(y Int)(lock1 Int)(v11 Int)(v21 Int)(v31 Int)(x1 Int)(y1 Int)) (=> (and (inv lock v1 v2 v3 x y) (not (= x y)) (or (and (= lock1 1) (= x1 y)) (and (= lock1 0) (= x1 y) (= y1 (+ y 1))))) (inv lock1 v11 v21 v31 x1 y1))))
     ; Property
     (assert (forall ((lock Int)(v1 Int)(v2 Int)(v3 Int)(x Int)(y Int)) (=> (and (inv lock v1 v2 v3 x y)(= x y)) (= lock 1) )))
     (check-sat)
     (get-model)