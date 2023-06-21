(set-logic HORN)
(declare-fun inv (Int Int Int) Bool)

; Initial condition 
(assert (forall ((i Int)(size Int)(sn Int)) (=> ( and (= sn 0) (= i 1)) (inv i size sn))))

; Transition relation 
(assert (forall ((i Int)(size Int)(sn Int)(i1 Int)(sn1 Int)) (=> (and (inv i size sn) (<= i size) (= i1 (+ i 1)) (= sn1 (+ sn 1))) (inv i1 size sn1))))

; Property
(assert (forall ((i Int)(size Int)(sn Int)) (=> (and (inv i size sn)(not (<= i size))) (or (= sn size) (= sn 0)))))

(check-sat)
(get-model)