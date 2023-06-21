(set-logic HORN)
(declare-fun inv (Int Int Int) Bool)

; Initial condition
(assert (forall ((x Int) (y Int) (z Int)) (=> (and (= x 0)) (inv x y z))))

; Transition relation
(assert (forall ((x Int) (y Int) (z Int) (x1 Int) (y1 Int)) (=> (and (inv x y z) (< x 5) (= x1 (+ x 1)) (ite (<= z y) (= y1 z) (= y1 y))) (inv x1 y1 z))))

; Property
(assert (forall ((x Int) (y Int) (z Int)) (=> (and (inv x y z) (not (< x 5))) (>= z y))))

(check-sat)
(get-model)