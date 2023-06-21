(set-logic HORN)
(declare-fun inv (Int Int Int Int) Bool)

; Initial condition
(assert (forall ((n Int) (v1 Int) (v2 Int) (v3 Int) (x Int) (y Int))
         (=> (and (= x 1)) (inv n v1 v2 v3 x y))))

; Transition relation
(assert (forall ((n Int) (v1 Int) (v2 Int) (v3 Int) (x Int) (y Int) (x1 Int) (y1 Int))
         (=> (and (inv n v1 v2 v3 x y) (<= x n) (= y (- n x)) (= x1 (+ x 1)) (= y1 y))
             (inv n v1 v2 v3 x1 y1))))

; Property
(assert (forall ((n Int) (v1 Int) (v2 Int) (v3 Int) (x Int) (y Int))
         (=> (and (inv n v1 v2 v3 x y) (not (<= x n)) (> n 0))
             (>= y 0))))

(check-sat)
(get-model)