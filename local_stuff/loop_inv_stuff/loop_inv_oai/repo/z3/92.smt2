(set-logic HORN)
(declare-fun inv (Int Int Int) Bool)

; Initial condition
(assert (forall ((x Int) (y Int) (z1 Int) (z2 Int) (z3 Int))
                (=> (and (= x 0) (= y 0)) (inv x y z1))))

; Transition relation
(assert (forall ((x Int) (y Int) (z1 Int) (z2 Int) (z3 Int) (x1 Int) (y1 Int) (z1_1 Int) (z2_1 Int) (z3_1 Int))
                (=> (and (inv x y z1) (>= y 0) (= y1 (+ y x)) (= x1 x) (= z1_1 z1) (= z2_1 z2) (= z3_1 z3))
                    (inv x1 y1 z1_1))))

; Property
(assert (forall ((x Int) (y Int) (z1 Int) (z2 Int) (z3 Int))
                (=> (and (inv x y z1) (not (>= y 0))) (>= y 0))))

(check-sat)
(get-model)