 (set-logic HORN)
     (declare-fun inv (Int Int) Bool)
     ; Initial condition
     (assert (forall ((x Int)(n Int)) (=> ( and (= x 0)) (inv x n))))
     ; Transition relation
     (assert (forall ((x Int)(n Int)(x1 Int)) (=> (and (inv x n) (< x n) (= x1 (+ x 1))) (inv x1 n))))
     ; Property
     (assert (forall ((x Int)(n Int)) (=> (and (inv x n)(not (< x n)) (>= n 0)) (= x n) )))
     (check-sat)
     (get-model)