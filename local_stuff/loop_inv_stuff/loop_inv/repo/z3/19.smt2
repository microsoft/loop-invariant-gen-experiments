 (set-logic HORN)
     (declare-fun inv (Int Int Int) Bool)
     ; Initial condition
     (assert (forall ((x Int)(m Int)(n Int)) (=> ( and (= x 0) (= m 0)) (inv x m n))))
     ; Transition relation
     (assert (forall ((x Int)(m Int)(n Int)(x1 Int)(m1 Int)) (=> (and (inv x m n) (< x n) (= x1 (+ x 1)) (or (= m1 m) (= m1 x))) (inv x1 m1 n))))
     ; Property
     (assert (forall ((x Int)(m Int)(n Int)) (=> (and (inv x m n)(not (< x n))(> n 0)) (< m n) )))
     (check-sat)
     (get-model)