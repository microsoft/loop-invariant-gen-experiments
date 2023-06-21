 (set-logic HORN)
     (declare-fun inv (Int Int Int Int) Bool)
     ; Initial condition
     (assert (forall ((x Int)(size Int)(y Int)(z Int)) (=> (and (= x 0)) (inv x size y z))))
     ; Transition relation
     (assert (forall ((x Int)(size Int)(y Int)(z Int)(x1 Int)(y1 Int)) (=> (and (inv x size y z) (< x size) (= x1 (+ x 1)) (ite (<= z y) (= y1 z) (= y1 y))) (inv x1 size y1 z))))
     ; Property
     (assert (forall ((x Int)(size Int)(y Int)(z Int)) (=> (and (inv x size y z)(not (< x size)) (> size 0)) (>= z y) )))
     (check-sat)
     (get-model)