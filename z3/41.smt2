 (set-logic HORN)
     (declare-fun inv (Int Int) Bool)
     ; Initial condition
     (assert (forall ((c Int)(n Int)) (=> (and (= c 0) (> n 0)) (inv c n))))
     ; Transition relation
     (assert (forall ((c Int)(n Int)(c1 Int)(n1 Int)) (=> (and (inv c n) (or (and (not (<= c n)) (= c1 (+ c 1)) (= n1 n)) (and (not (= c n)) (= c1 1) (= n1 n)) (and (not (or (not (<= c n)) (not (= c n)))) (= c1 c) (= n1 n)))) (inv c1 n1))))
     ; Property
     (assert (forall ((c Int)(n Int)) (=> (and (inv c n) (not true)) (=> (not (= c n)) (<= c n)))))
     (check-sat)
     (get-model)