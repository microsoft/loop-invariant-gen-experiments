 (set-logic HORN)
     (declare-fun inv (Int Int) Bool)
     ; Initial condition
     (assert (forall ((x Int)(n Int)) (=> (and (= x n)) (inv x n))))
     ; Transition relation
     (assert (forall ((x Int)(n Int)(x1 Int)) (=> (and (inv x n) (> x 1) (= x1 (- x 1))) (inv x1 n))))
     ; Property
     (assert (forall ((x Int)(n Int)) (=> (and (inv x n)(not (> x 1)) (not (= x 1))) (< n 0))))
     (check-sat)
     (get-model)