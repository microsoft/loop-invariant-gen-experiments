(set-logic HORN)
(declare-fun inv (Int Int) Bool)

; Initial condition
(assert (forall ((c Int)(n Int)) (=> (and (= c 0) (> n 0)) (inv c n))))

; Transition relation
(assert (forall ((c Int)(n Int)(c1 Int)) (=> (and (inv c n) (not (= c n))) (=> (inv (+ c 1) n) (= c1 (+ c 1))))))

(assert (forall ((c Int)(n Int)(c1 Int)) (=> (and (inv c n) (= c n)) (=> (inv 1 n) (= c1 1)))))

; Property
(assert (forall ((c Int)(n Int)) (=> (and (inv c n) (not (= c n))) (<= c n))))

(check-sat)
(get-model)