(set-logic HORN)
(declare-fun inv (Int Int) Bool)

; Initial condition
(assert (forall ((n Int) (c Int)) (=> (and (> n 0) (= c 0)) (inv n c))))

; Transition relation
(assert (forall ((n Int) (c Int) (c1 Int) (nondet Bool))
  (=> (and (inv n c) nondet)
      (ite (= c n)
           (and (= c1 1) (inv n c1))
           (and (= c1 (+ c 1)) (inv n c1))))))

; Property
(assert (forall ((n Int) (c Int))
  (=> (and (inv n c) (= c n)) (>= c 0))))

(check-sat)
(get-model)