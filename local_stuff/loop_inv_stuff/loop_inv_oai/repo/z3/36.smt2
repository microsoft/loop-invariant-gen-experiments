(set-logic HORN)
(declare-fun inv (Int) Bool)

; Initial condition
(assert (forall ((c Int)) (=> (= c 0) (inv c))))

; Transition relation
(assert (forall ((c Int)(c1 Int)(nondet1 Bool)(nondet2 Bool)) (=> (and (inv c) (or (and nondet1 (not (= c 40)) (= c1 (+ c 1))) (and (not nondet1) (= c 40) (= c1 1)))) (inv c1))))

; Property
(assert (forall ((c Int)) (=> (and (inv c) (not (= c 40))) (<= c 40))))

(check-sat)
(get-model)