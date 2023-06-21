 (set-logic HORN)
     (declare-fun inv (Int Int Int Int Int Int) Bool)
     ; Initial condition
     (assert (forall ((d1 Int)(d2 Int)(d3 Int)(x1 Int)(x2 Int)(x3 Int)) (=> (and (= d1 1) (= d2 1) (= d3 1) (= x1 1)) (inv d1 d2 d3 x1 x2 x3))))
     ; Transition relation
     (assert (forall ((d1 Int)(d2 Int)(d3 Int)(x1 Int)(x2 Int)(x3 Int)(x1_1 Int)(x2_1 Int)(x3_1 Int)) (=> (and (inv d1 d2 d3 x1 x2 x3) (> x1 0) (> x2 0) (> x3 0) (= x1_1 (- x1 d1)) (= x2_1 (- x2 d2)) (= x3_1 (- x3 d3))) (inv d1 d2 d3 x1_1 x2_1 x3_1))))
     ; Property
     (assert (forall ((d1 Int)(d2 Int)(d3 Int)(x1 Int)(x2 Int)(x3 Int)) (=> (and (inv d1 d2 d3 x1 x2 x3)(not (> x1 0))) (>= x2 0))))
     (check-sat)
     (get-model)