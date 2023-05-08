 (set-logic HORN)
     (declare-fun inv (Int Int) Bool)
     ; Initial condition
     (assert (forall ((c Int)(n Int)) (=> (and (= c 0) (> n 0)) (inv c n))))
     ; Transition relation
     (assert (forall ((c Int)(n Int)(c1 Int)) (=> (and (inv c n) (or (and (> c n) (= c1 (+ c 1))) (and (= c n) (= c1 1)))) (inv c1 n))))
     ; Property
     (assert (forall ((c Int)(n Int)) (=> (and (inv c n)(not (exists ((c1 Int)) (or (and (> c n) (= c1 (+ c 1))) (and (= c n) (= c1 1)))))) (not (= c n)))))
     (check-sat)
     (get-model)