 (set-logic HORN)
     (declare-fun inv (Int) Bool)
     ; Initial condition
     (assert (forall ((x Int)) (=> (= x 10000) (inv x))))
     ; Transition relation
     (assert (forall ((x Int)(x1 Int)) (=> (and (inv x) (> x 0) (= x1 (- x 1))) (inv x1))))
     ; Property
     (assert (forall ((x Int)) (=> (and (inv x)(not (> x 0))) (= x 0))))
     (check-sat)
     (get-model)