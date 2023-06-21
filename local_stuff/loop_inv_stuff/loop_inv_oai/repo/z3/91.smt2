(set-logic HORN)
(declare-fun inv (Int Int) Bool)

; Initial condition
(assert (forall ((x Int)(y Int)) (=> (and (= x 0) (= y 0)) (inv x y))))

; Transition relation
(assert (forall ((x Int)(y Int)(y1 Int)) (=> (and (inv x y) (>= y 0) (= y1 (+ y x))) (inv x y1))))

; Property
(assert (forall ((x Int)(y Int)) (=> (and (inv x y) (not (>= y 0))) (>= y 0))))

(check-sat)
(get-model)