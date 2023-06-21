(set-logic HORN)
(declare-fun inv (Int Int) Bool)

; Initial condition
(assert (forall ((x Int)(y Int)) (=> (and (= x 1)) (inv x y))))

; Transition relation
(assert (forall ((x Int)(y Int)(x1 Int)(y1 Int)) (=> (and (inv x y) (<= x 100) (= y1 (- 100 x)) (= x1 (+ x 1))) (inv x1 y1))))

; Property
(assert (forall ((x Int)(y Int)) (=> (and (inv x y) (not (<= x 100))) (>= y 0))))

(check-sat)
(get-model)