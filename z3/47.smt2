 (set-logic HORN)
     (declare-fun inv (Int Int) Bool)
     ; Initial condition
     (assert (forall ((c Int)(n Int)) (=> ( and (= c 0) (> n 0)) (inv c n))))
     ; Transition relation
     (assert (forall ((c Int)(n Int)(c1 Int)(n1 Int)) (=> (and (inv c n) (= n1 n) (or (and (not (= c n)) (= c1 (+ c 1))) (and (= c n) (= c1 1)) (and (not (or (and (not (= c n)) (= c1 (+ c 1))) (and (= c n) (= c1 1)))) (= c1 c)))) (inv c1 n1))))
     ; Property
     (assert (forall ((c Int)(n Int)) (=> (and (inv c n)) (or (not (< c 0)) (not (> c n)) (= c n)) )))
     (check-sat)
     (get-model)