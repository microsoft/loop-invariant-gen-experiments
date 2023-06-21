(set-logic HORN)
(declare-fun inv (Int Int) Bool)

; Initial condition
(assert (forall ((sn Int)(x Int)) (=> (and (= sn 0) (= x 0)) (inv sn x))))

; Transition relation
(assert (forall ((sn Int)(x Int)(sn1 Int)(x1 Int)) (=> (and (inv sn x) (= x1 (+ x 1)) (= sn1 (+ sn 1))) (inv sn1 x1))))

; Property
(assert (forall ((sn Int)(x Int)) (=> (and (inv sn x)(not (= sn x))) (= sn (- 1)))))

(check-sat)
(get-model)