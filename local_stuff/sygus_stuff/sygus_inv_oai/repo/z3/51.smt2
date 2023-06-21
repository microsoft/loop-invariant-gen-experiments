(set-logic HORN)
(declare-fun inv (Int) Bool)
(declare-fun unknown1 () Bool)
(declare-fun unknown2 () Bool)

; Initial condition
(assert (forall ((c Int)) (=> (= c 0) (inv c))))

; Transition relation
(assert (forall ((c Int) (c1 Int))
  (=> (and (inv c) (ite unknown1 (ite unknown2 (and (not (= c 4)) (= c1 (+ c 1))) (= c1 c)) (ite (= c 4) (= c1 1) (= c1 c))))
       (inv c1))))

; Property
(assert (forall ((c Int)) (=> (and (inv c) (not (= c 4))) (<= c 4))))

(check-sat)
(get-model)