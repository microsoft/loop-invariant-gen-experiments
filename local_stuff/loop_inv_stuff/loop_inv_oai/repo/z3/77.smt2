(set-logic HORN)
(declare-fun inv (Int Int Int) Bool)

; Initial condition 
(assert (forall ((i Int)(x Int)(y Int)) (=> (and (= i 0) (>= x 0) (>= y 0) (>= x y)) (inv i x y))))

; Transition relation 
(assert (forall ((i Int)(x Int)(y Int)(i1 Int)) (=> (and (inv i x y) (unknown) (< i y) (= i1 (+ i 1))) (inv i1 x y))))

; Transition relation (no change)
(assert (forall ((i Int)(x Int)(y Int)) (=> (and (inv i x y) (unknown) (not (< i y))) (inv i x y))))

; Property
(assert (forall ((i Int)(x Int)(y Int)) (=> (and (inv i x y) (not (unknown)) (< i y)) (< i x))))

(check-sat)
(get-model)