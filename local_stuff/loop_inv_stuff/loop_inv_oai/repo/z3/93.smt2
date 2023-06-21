(set-logic HORN)
(declare-fun inv (Int Int Int Int) Bool)

; Initial condition
(assert (forall ((i Int)(n Int)(x Int)(y Int)) (=> (and (>= n 0) (= i 0) (= x 0) (= y 0)) (inv i n x y))))

; Transition relation
(assert (forall ((i Int)(n Int)(x Int)(y Int)(i1 Int)(x1 Int)(y1 Int)) (=> (and (inv i n x y) (< i n) (= i1 (+ i 1)))
  (or (and (= x1 (+ x 1)) (= y1 (+ y 2)))
      (and (= x1 (+ x 2)) (= y1 (+ y 1))))
  )
  (inv i1 n x1 y1)
)))

; Property
(assert (forall ((i Int)(n Int)(x Int)(y Int)) (=> (and (inv i n x y) (not (< i n))) (= (* 3 n) (+ x y)))))

(check-sat)
(get-model)