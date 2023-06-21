(set-logic HORN)
(declare-fun inv (Int Int Int Int) Bool)

; Initial condition
(assert (forall ((i Int)(j Int)(k Int)(n Int)) (=> (and (>= k 0) (>= n 0) (= i 0) (= j 0)) (inv i j k n))))

; Transition relation
(assert (forall ((i Int)(j Int)(k Int)(n Int)(i1 Int)(j1 Int)) (=> (and (inv i j k n) (<= i n) (= i1 (+ i 1)) (= j1 (+ j i1))) (inv i1 j1 k n))))

; Property
(assert (forall ((i Int)(j Int)(k Int)(n Int)) (=> (and (inv i j k n) (not (<= i n))) (> (+ i (+ j k)) (* 2 n)))))

(check-sat)
(get-model)