 (set-logic HORN)
     (declare-fun inv (Int Int) Bool)
     ; Initial condition
     (assert (forall ((c Int)(z Int)(y Int)) (=> (and (= c 0) (>= y 0) (>= y 127) (= z (* 36 y))) (inv c z))))
     ; Transition relation
     (assert (forall ((c Int)(z Int)(c1 Int)(z1 Int)) (=> (and (inv c z) (unknown) (< c 36) (= z1 (+ z 1)) (= c1 (+ c 1))) (inv c1 z1))))
     ; Property
     (assert (forall ((c Int)(z Int)) (=> (and (inv c z) (not (unknown)) (< c 36)) (>= z 0))))
     (check-sat)
     (get-model)