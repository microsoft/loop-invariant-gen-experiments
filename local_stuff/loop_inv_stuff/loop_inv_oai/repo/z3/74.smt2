(set-logic HORN)
(declare-fun inv (Int Int Int Int Int) Bool)

; Initial condition
(assert (forall ((c Int)(x1 Int)(x2 Int)(x3 Int)(y Int)(z Int)) (=> (and (= c 0) (>= y 0) (>= y 127) (= z (* 36 y))) (inv c x1 x2 x3 y z))))

; Transition relation
(assert (forall ((c Int)(x1 Int)(x2 Int)(x3 Int)(y Int)(z Int)(c1 Int)(z1 Int)) (=> (and (inv c x1 x2 x3 y z) (< c 36) (= z1 (+ z 1)) (= c1 (+ c 1))) (inv c1 x1 x2 x3 y z1))))

; Property
(assert (forall ((c Int)(x1 Int)(x2 Int)(x3 Int)(y Int)(z Int)) (=> (and (inv c x1 x2 x3 y z) (not (< c 36))) (>= z 0))))

(check-sat)
(get-model)