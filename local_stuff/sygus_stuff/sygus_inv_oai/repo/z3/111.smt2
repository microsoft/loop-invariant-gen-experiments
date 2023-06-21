(set-logic HORN)
(declare-fun inv (Int Int Int) Bool)

; Initial condition 
(assert (forall ((i Int)(n Int)(sn Int)) (=> ( and (= sn 0) (= i 1)) (inv i n sn))))

; Transition relation 
(assert (forall ((i Int)(n Int)(sn Int)(i1 Int)(sn1 Int)) (=> (and (inv i n sn) (<= i n) (= i1 (+ i 1)) (= sn1 (+ sn 1))) (inv i1 n sn1))))

; Property
(assert (forall ((i Int)(n Int)(sn Int)) (=> (and (inv i n sn)(not (<= i n)) (not (= sn 0))) (= sn n))))

(check-sat)
(get-model)