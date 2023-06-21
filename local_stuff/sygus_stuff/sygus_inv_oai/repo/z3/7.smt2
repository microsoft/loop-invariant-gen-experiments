(set-logic HORN)
(declare-fun inv (Int Int) Bool)

; Initial condition
(assert (forall ((x Int)(y Int)) (=> (and (>= x 0) (<= x 10) (<= y 10) (>= y 0)) (inv x y))))

; Transition relation
(assert (forall ((x Int)(y Int)(x1 Int)(y1 Int)) (=> (and (inv x y) (= x1 (+ x 10)) (= y1 (+ y 10))) (inv x1 y1))))

; Property
(assert (forall ((x Int)(y Int)) (=> (and (inv x y) (= x 20)) (not (= y 0)))))

(check-sat)
(get-model)