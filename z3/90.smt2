 (set-logic HORN)
     (declare-fun inv (Int Int Int Int Int Int) Bool)
     ; Initial condition
     (assert (forall ((x Int)(y Int)(lock Int)(v1 Int)(v2 Int)(v3 Int)) (=> (and (= y (+ x 1)) (= lock 0)) (inv x y lock v1 v2 v3))))
     ; Transition relation
     (assert (forall ((x Int)(y Int)(lock Int)(v1 Int)(v2 Int)(v3 Int)(x1 Int)(y1 Int)(lock1 Int)(v11 Int)(v21 Int)(v31 Int)) (=> (and (inv x y lock v1 v2 v3) (not (= x y)) (or (and (= lock1 1) (= x1 y)) (and (= lock1 0) (= x1 y) (= y1 (+ y 1))))) (inv x1 y1 lock1 v11 v21 v31))))
     ; Property
     (assert (forall ((x Int)(y Int)(lock Int)(v1 Int)(v2 Int)(v3 Int)) (=> (and (inv x y lock v1 v2 v3)(= x y)) (= lock 1))))
     (check-sat)
     (get-model)