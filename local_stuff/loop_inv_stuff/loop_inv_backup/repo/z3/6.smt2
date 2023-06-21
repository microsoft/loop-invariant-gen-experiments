 (set-logic HORN)
     (declare-fun inv (Int Int Int Int Int) Bool)
     ; Initial condition
     (assert (forall ((v1 Int)(v2 Int)(v3 Int)(x Int)(size Int)(y Int)(z Int)) (=> (and (= x 0)) (inv v1 v2 v3 x size y z))))
     ; Transition relation
     (assert (forall ((v1 Int)(v2 Int)(v3 Int)(x Int)(size Int)(y Int)(z Int)(x1 Int)(y1 Int)) (=> (and (inv v1 v2 v3 x size y z) (< x size) (= x1 (+ x 1)) (ite (<= z y) (= y1 z) (= y1 y))) (inv v1 v2 v3 x1 size y1 z))))
     ; Property
     (assert (forall ((v1 Int)(v2 Int)(v3 Int)(x Int)(size Int)(y Int)(z Int)) (=> (and (inv v1 v2 v3 x size y z)(not (< x size))(> size 0)) (>= z y))))
     (check-sat)
     (get-model)