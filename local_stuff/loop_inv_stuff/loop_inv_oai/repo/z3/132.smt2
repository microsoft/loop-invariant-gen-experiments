(set-logic HORN)
(declare-fun inv (Int Int) Bool)

; Initial condition
(assert (forall ((i Int)(j Int)(c Int)(t Int)) (=> (and (= i 0)) (inv i j))))

; Transition relation
(assert (forall ((i Int)(j Int)(c Int)(t Int)(i1 Int)(j1 Int)(c1 Int)(t1 Int)) (=> (and (inv i j) (or (<= c 48) (>= c 57)) ) (inv i1 j1))))

(assert (forall ((i Int)(j Int)(c Int)(t Int)(i1 Int)(j1 Int)(c1 Int)(t1 Int)) (=> (and (inv i j) (> c 48) (< c 57) (= j1 (+ i i)) (= t1 (- c 48)) (= i1 (+ j1 t1)) ) (inv i1 j1))))

; Property
(assert (forall ((i Int)(j Int)(c Int)(t Int)) (=> (and (inv i j) (or (<= c 48) (>= c 57))) (>= i 0))))

(check-sat)
(get-model)