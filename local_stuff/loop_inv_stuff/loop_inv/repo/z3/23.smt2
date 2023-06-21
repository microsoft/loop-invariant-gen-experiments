 (set-logic HORN)
     (declare-fun inv (Int Int) Bool)
     ; Initial condition
     (assert (forall ((i Int)(j Int)) (=> ( and (= i 1) (= j 20)) (inv i j))))
     ; Transition relation
     (assert (forall ((i Int)(j Int)(i1 Int)(j1 Int)) (=> (and (inv i j) (>= j i) (= i1 (+ i 2)) (= j1 (- j 1)) ) (inv i1 j1))))
     ; Property
     (assert (forall ((i Int)(j Int)) (=> (and (inv i j)(not (>= j i))) (= j 13) )))
     (check-sat)
     (get-model)