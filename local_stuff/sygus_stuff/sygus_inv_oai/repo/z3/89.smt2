(set-logic HORN)
(declare-fun inv (Int Int Int) Bool)

; Initial condition
(assert (forall ((x Int)(y Int)(lock Int)) (=> (and (= x y) (= lock 1)) (inv x y lock))))

; Transition relation
(assert (forall ((x Int)(y Int)(lock Int)(x1 Int)(y1 Int)(lock1 Int)) (=> (and (inv x y lock) (not (= x y)) (ite (unknown) (and (= lock1 1) (= x1 y) (= y1 y)) (and (= lock1 0) (= x1 y) (= y1 (+ y 1))))) (inv x1 y1 lock1))))

; Property
(assert (forall ((x Int)(y Int)(lock Int)) (=> (and (inv x y lock) (= x y)) (= lock 1))))

(check-sat)
(get-model)