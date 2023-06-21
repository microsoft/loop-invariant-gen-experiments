(set-logic HORN)
(declare-fun inv (Int Int Int) Bool)

; Initial condition
(assert (forall ((x Int) (m Int) (n Int)) (=> (and (= x 1) (= m 1)) (inv x m n))))

; Transition relation
(assert (forall ((x Int) (m Int) (n Int) (x1 Int) (m1 Int))
                (=> (and (inv x m n) (< x n)
                         (ite (exists ((unknown Bool)) unknown)
                              (= m1 x)
                              (= m1 m))
                         (= x1 (+ x 1)))
                    (inv x1 m1 n))))

; Property
(assert (forall ((x Int) (m Int) (n Int))
                (=> (and (inv x m n) (not (< x n)) (> n 1))
                    (and (< m n))))) ; Removed the second assertion as it is redundant

(check-sat)
(get-model)