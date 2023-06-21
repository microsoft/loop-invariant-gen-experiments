 (set-logic HORN)
     (declare-fun inv (Int Int) Bool)
     ; Initial condition
     (assert (forall ((c Int)(n Int)) (=> (and (= c 0) (> n 0)) (inv c n))))
     ; Transition relation
     (assert (forall ((c Int)(n Int)(c1 Int)) (=> (and (inv c n) (= c1 (ite (and (not (= c n)) true) (+ c 1) (ite (and (= c n) false) 1 c)))) (inv c1 n))))
     ; Property
     (assert (forall ((c Int)(n Int)) (=> (and (inv c n) (not true)) (=> (not (= c n)) (<= c n)))))
     (check-sat)
     (get-model)