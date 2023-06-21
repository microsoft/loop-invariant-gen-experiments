(set-logic HORN)
(declare-fun inv (Int Int Int Int Int) Bool)

; Initial condition
(assert (forall ((c Int)(n Int)(v1 Int)(v2 Int)(v3 Int)) (=> (and (= c 0) (> n 0)) (inv c n v1 v2 v3))))

; Transition relation
(assert (forall ((c Int)(n Int)(v1 Int)(v2 Int)(v3 Int)(c1 Int)(n1 Int)(v11 Int)(v21 Int)(v31 Int)) (=> (and (inv c n v1 v2 v3) (or (and (not (= c n)) (= c1 (+ c 1)) (= n1 n) (= v11 v1) (= v21 v2) (= v31 v3)) (and (= c n) (= c1 1) (= n1 n) (= v11 v1) (= v21 v2) (= v31 v3)))) (inv c1 n1 v11 v21 v31))))

; Property
(assert (forall ((c Int)(n Int)(v1 Int)(v2 Int)(v3 Int)) (=> (and (inv c n v1 v2 v3) (not (= c n))) (<= c n))))

(check-sat)
(get-model)