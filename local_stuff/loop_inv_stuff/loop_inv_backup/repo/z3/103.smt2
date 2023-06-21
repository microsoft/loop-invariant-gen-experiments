 (set-logic HORN)
     (declare-fun inv (Int) Bool)
     ; Initial condition
     (assert (forall ((x Int)) (=> (= x 0) (inv x))))
     ; Transition relation
     (assert (forall ((x Int)(x1 Int)) (=> (and (inv x) (< x 100) (= x1 (+ x 1))) (inv x1))))
     ; Property
     (assert (forall ((x Int)) (=> (and (inv x)(not (< x 100))) (= x 100))))
     (check-sat)
     (get-model)