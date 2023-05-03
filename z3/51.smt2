 (set-logic HORN)
     (declare-fun inv (Int) Bool)
     ; Initial condition
     (assert (forall ((c Int)) (=> (= c 0) (inv c))))
     ; Transition relation
     (assert (forall ((c Int)(c1 Int)) (=> (and (inv c) (not (= c 4)) (= c1 (+ c 1))) (inv c1))))
     (assert (forall ((c Int)(c1 Int)) (=> (and (inv c) (= c 4) (= c1 1)) (inv c1))))
     ; Property
     (assert (forall ((c Int)) (=> (and (inv c) (not (= c 4))) (<= c 4))))
     (check-sat)
     (get-model)