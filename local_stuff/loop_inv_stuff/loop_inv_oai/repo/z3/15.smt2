(set-logic HORN)
(declare-fun inv (Int Int Int) Bool)

; Initial condition
(assert (forall ((x Int) (m Int) (n Int)) (=> (and (= x 0) (= m 0)) (inv x m n))))

; Transition relation
(assert (forall ((x Int) (m Int) (n Int) (x1 Int) (m1 Int)) (=> (and (inv x m n) (< x n) (= x1 (+ x 1))) (or (and (= m1 m) (inv x1 m1 n)) (and (= m1 x) (inv x1 m1 n))))))

; Property
(assert (forall ((x Int) (m Int) (n Int)) (=> (and (inv x m n) (not (< x n)) (> n 0)) (< m n))))

(check-sat)
(get-model)

; The second assertion (m >= 0) is trivially true, as m is always assigned a value between 0 and n-1 in the loop.