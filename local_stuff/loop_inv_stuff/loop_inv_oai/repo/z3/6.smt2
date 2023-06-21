(set-logic HORN)
(declare-fun inv (Int Int Int Int Int Int) Bool)

; Initial condition
(assert (forall ((v1 Int) (v2 Int) (v3 Int) (x Int) (size Int) (y Int) (z Int))
         (=> (and (= x 0) (= v1 0) (= v2 0) (= v3 0))
             (inv v1 v2 v3 x size y z))))

; Transition relation
(assert (forall ((v1 Int) (v2 Int) (v3 Int) (x Int) (size Int) (y Int) (z Int)
                 (v1' Int) (v2' Int) (v3' Int) (x' Int) (y' Int) (z' Int))
         (=> (and (inv v1 v2 v3 x size y z) (< x size)
                  (= x' (+ x 1))
                  (ite (<= z y) (= y' z) (= y' y))
                  (= z' z)
                  (= v1' v1) (= v2' v2) (= v3' v3))
             (inv v1' v2' v3' x' size y' z'))))

; Property
(assert (forall ((v1 Int) (v2 Int) (v3 Int) (x Int) (size Int) (y Int) (z Int))
         (=> (and (inv v1 v2 v3 x size y z) (not (< x size)) (> size 0))
             (>= z y))))

(check-sat)
(get-model)