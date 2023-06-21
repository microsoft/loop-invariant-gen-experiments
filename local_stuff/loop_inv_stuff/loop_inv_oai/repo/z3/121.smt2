(set-logic HORN)
(declare-fun inv (Int Int) Bool)

; Initial condition
(assert (forall ((i Int)(sn Int)) (=> (and (= sn 0) (= i 1)) (inv i sn))))

; Transition relation
(assert (forall ((i Int)(sn Int)(i1 Int)(sn1 Int)) (=> (and (inv i sn) (<= i 8) (= i1 (+ i 1)) (= sn1 (+ sn 1))) (inv i1 sn1))))

; Property
(assert (forall ((i Int)(sn Int)) (=> (and (inv i sn) (not (<= i 8))) (=> (not (= sn 0)) (= sn 8)))))

(check-sat)
(get-model)