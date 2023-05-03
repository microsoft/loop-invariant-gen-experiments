 (set-logic HORN)
     (declare-fun inv (Int Int) Bool)
     ; Initial condition
     (assert (forall ((x Int)(n Int)) (=> (= x n) (inv x n))))
     ; Transition relation
     (assert (forall ((x Int)(n Int)(x1 Int)) (=> (and (inv x n) (> x 0) (= x1 (- x 1))) (inv x1 n))))
     ; Property
     (assert (forall ((x Int)(n Int)) (=> (and (inv x n)(not (> x 0))(>= n 0)) (= x 0))))
     (check-sat)
     (get-model)