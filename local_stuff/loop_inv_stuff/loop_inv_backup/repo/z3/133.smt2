 (set-logic HORN)
     (declare-fun inv (Int Int) Bool)
     ; Initial condition
     (assert (forall ((n Int)(x Int)) (=> (and (= x 0) (>= n 0)) (inv n x))))
     ; Transition relation
     (assert (forall ((n Int)(x Int)(x1 Int)) (=> (and (inv n x) (< x n) (= x1 (+ x 1))) (inv n x1))))
     ; Property
     (assert (forall ((n Int)(x Int)) (=> (and (inv n x)(not (< x n))) (= x n) )))
     (check-sat)
     (get-model)