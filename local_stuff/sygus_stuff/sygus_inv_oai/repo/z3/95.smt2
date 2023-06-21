(set-logic HORN)
(declare-fun inv (Int Int Int Int) Bool)

; Initial condition
(assert (forall ((i Int)(j Int)(x Int)(y Int)) (=> (and (= j 0) (= i 0) (= y 1)) (inv i j x y))))

; Transition relation
(assert (forall ((i Int)(j Int)(x Int)(y Int)(i1 Int)(j1 Int)) (=> (and (inv i j x y) (<= i x) (= i1 (+ i 1)) (= j1 (+ j y))) (inv i1 j1 x y))))

; Property
(assert (forall ((i Int)(j Int)(x Int)(y Int)) (=> (and (inv i j x y) (not (<= i x)) (= y 1)) (= i j))))

(check-sat)
(get-model)