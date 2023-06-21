(set-logic HORN)
(declare-fun inv (Int Int) Bool)

; Initial condition
(assert (forall ((n Int) (c Int)) (=> (and (> n 0) (= c 0)) (inv n c))))

; Transition relation
(assert (forall ((n Int) (c Int) (c1 Int) (nondet Bool))
  (=> (and (inv n c) (or (and (= c n) (= c1 1)) (and (not (= c n)) (= c1 (+ c 1)))))
      (inv n c1))))

; Property
(assert (forall ((n Int) (c Int))
  (=> (and (inv n c) (= c n)) (<= c n))))

(check-sat)
(get-model)