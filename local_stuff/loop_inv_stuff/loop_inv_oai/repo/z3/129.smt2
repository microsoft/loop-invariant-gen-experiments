(set-logic HORN)
(declare-fun inv (Int Int) Bool)

; Initial condition 
(assert (forall ((x Int)(y Int)) (=> ( and (= x 1)) (inv x y))))

; Transition relation 
(assert (forall ((x Int)(y Int)(x1 Int)) (=> (and (inv x y) (< x y) (= x1 (+ x x))) (inv x1 y))))

; Property
(assert (forall ((x Int)(y Int)) (=> (and (inv x y)(not (< x y))) (>= x 1) )))

(check-sat)
(get-model)