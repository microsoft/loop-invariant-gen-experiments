 (set-logic HORN)
     (declare-fun inv (Int Int Int) Bool)
     ; Initial condition
     (assert (forall ((c Int)(y Int)(z Int)) (=> (and (= c 0) (>= y 0) (>= y 127) (= z (* 36 y))) (inv c y z))))
     ; Transition relation
     (assert (forall ((c Int)(y Int)(z Int)(c1 Int)(z1 Int)) (=> (and (inv c y z) (< c 36) (= z1 (+ z 1)) (= c1 (+ c 1)) ) (inv c1 y z1))))
     ; Property
     (assert (forall ((c Int)(y Int)(z Int)) (=> (and (inv c y z)(not (< c 36))) (< z 4608) )))
     (check-sat)
     (get-model)