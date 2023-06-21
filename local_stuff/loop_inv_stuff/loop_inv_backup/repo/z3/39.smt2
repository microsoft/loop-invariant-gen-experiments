 (set-logic HORN)
     (declare-fun inv (Int Int) Bool)
     ; Initial condition
     (assert (forall ((n Int)(c Int)) (=> (and (> n 0) (= c 0)) (inv n c))))
     ; Transition relation
     (assert (forall ((n Int)(c Int)(n1 Int)(c1 Int)) (=> (and (inv n c) (ite (= c n) (= c1 1) (= c1 (+ c 1)))) (inv n1 c1))))
     ; Property
     (assert (forall ((n Int)(c Int)) (=> (and (inv n c) (= c n)) (<= c n))))
     (check-sat)
     (get-model)