 (set-logic HORN)
     (declare-fun inv (Int Int Int Int Int Int) Bool)
     ; Initial condition
     (assert (forall ((c Int)(x1 Int)(x2 Int)(x3 Int)(y Int)(z Int)) (=> (and (= c 0) (>= y 0) (>= y 127) (= z (* 36 y))) (inv c x1 x2 x3 y z))))
     ; Transition relation
     (assert (forall ((c Int)(x1 Int)(x2 Int)(x3 Int)(y Int)(z Int)(c1 Int)(x11 Int)(x21 Int)(x31 Int)(y1 Int)(z1 Int)) (=> (and (inv c x1 x2 x3 y z) (< c 36) (= z1 (+ z 1)) (= c1 (+ c 1)) (= x11 x1) (= x21 x2) (= x31 x3) (= y1 y)) (inv c1 x11 x21 x31 y1 z1))))
     ; Property
     (assert (forall ((c Int)(x1 Int)(x2 Int)(x3 Int)(y Int)(z Int)) (=> (and (inv c x1 x2 x3 y z)(not (< z 0)) (>= z 4608)) (>= c 36) )))
     (check-sat)
     (get-model)