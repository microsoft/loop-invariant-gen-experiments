(set-logic HORN)
(declare-fun inv (Int Int Int Int Int Int) Bool)

; Initial condition
(assert (forall ((i Int)(x Int)(y Int)(z1 Int)(z2 Int)(z3 Int)) (=> (and (= i 0) (>= x 0) (>= y 0) (>= x y)) (inv i x y z1 z2 z3))))

; Transition relation
(assert (forall ((i Int)(x Int)(y Int)(z1 Int)(z2 Int)(z3 Int)(i1 Int)(x1 Int)(y1 Int)(z11 Int)(z21 Int)(z31 Int)) (=> (and (inv i x y z1 z2 z3) (< i y) (= i1 (+ i 1)) (= x1 x) (= y1 y) (= z11 z1) (= z21 z2) (= z31 z3)) (inv i1 x1 y1 z11 z21 z31))))

(assert (forall ((i Int)(x Int)(y Int)(z1 Int)(z2 Int)(z3 Int)(i1 Int)(x1 Int)(y1 Int)(z11 Int)(z21 Int)(z31 Int)) (=> (and (inv i x y z1 z2 z3) (not (< i y)) (= i1 i) (= x1 x) (= y1 y) (= z11 z1) (= z21 z2) (= z31 z3)) (inv i1 x1 y1 z11 z21 z31))))

; Property
(assert (forall ((i Int)(x Int)(y Int)(z1 Int)(z2 Int)(z3 Int)) (=> (and (inv i x y z1 z2 z3) (not (exists ((nondet Bool)) nondet)) (>= i x) (< 0 i)) (>= i y))))

(check-sat)
(get-model)