(set-logic HORN)
(declare-fun inv (Int Int) Bool)

; Initial condition
(assert (forall ((x Int) (y Int)) (=> (and (>= x 0) (<= x 2) (<= y 2) (>= y 0)) (inv x y))))

; Transition relation
(assert (forall ((x Int) (y Int) (x1 Int) (y1 Int)) (=> (and (inv x y) (= x1 (+ x 2)) (= y1 (+ y 2))) (inv x1 y1))))

; Property
(assert (forall ((x Int) (y Int)) (=> (and (inv x y) (= x 4)) (not (= y 0)))))

(check-sat)
(get-model)