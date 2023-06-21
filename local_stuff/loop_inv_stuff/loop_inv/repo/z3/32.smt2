 (set-logic HORN)
     (declare-fun inv (Int Int) Bool)
     ; Initial condition
     (assert (forall ((n Int)(x Int)) (=> ( and (= x n)) (inv n x))))
     ; Transition relation
     (assert (forall ((n Int)(x Int)(x1 Int)) (=> (and (inv n x) (> x 1) (= x1 (- x 1))) (inv n x1))))
     ; Property
     (assert (forall ((n Int)(x Int)) (=> (and (inv n x)(not (> x 1)) (>= n 0)) (= x 1) )))
     (check-sat)
     (get-model)