 (set-logic HORN)
     (declare-fun inv (Int Int Int) Bool)
     ; Initial condition
     (assert (forall ((c Int)(y Int)(z Int)) (=> (and (= c 0) (>= y 0) (>= y 127) (= z (* 36 y))) (inv c y z))))
     ; Transition relation
     (assert (forall ((c Int)(y Int)(z Int)(c1 Int)(y1 Int)(z1 Int)) (=> (and (inv c y z) (exists ((nondet Bool)) nondet) (ite (< c 36) (and (= z1 (+ z 1)) (= c1 (+ c 1)) (= y1 y)) (and (= z1 z) (= c1 c) (= y1 y)))) (inv c1 y1 z1))))
     ; Property
     (assert (forall ((c Int)(y Int)(z Int)) (=> (and (inv c y z)(not (exists ((nondet Bool)) nondet))) (=> (< c 36) (>= z 0)) )))
     (check-sat)
     (get-model)