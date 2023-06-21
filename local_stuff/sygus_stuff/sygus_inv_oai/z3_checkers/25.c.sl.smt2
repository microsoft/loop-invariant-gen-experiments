(set-logic LIA)

(define-fun inv-f ((x Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int)) Bool (or (not (= x x_2)) (>= x_2 1) (= x_2 0)))



(define-fun pre-f ((x Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int)) Bool

    (and (= x x_1) (= x_1 10000)))

(define-fun trans-f ((x Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (x! Int) (x_0! Int) (x_1! Int) (x_2! Int) (x_3! Int)) Bool

    (or (and (= x_2 x) (= x_2 x!)) (and (= x_2 x) (> x_2 0) (= x_3 (- x_2 1)) (= x_3 x!))))

(define-fun post-f ((x Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int)) Bool

    (or (not (= x x_2)) (not (and (not (> x_2 0)) (not (= x_2 0))))))





(declare-const v0 Int)
(declare-const v0! Int)
(declare-const v1 Int)
(declare-const v1! Int)
(declare-const v2 Int)
(declare-const v2! Int)
(declare-const v3 Int)
(declare-const v3! Int)
(declare-const v4 Int)
(declare-const v4! Int)

(assert
    (or
        (not (=> 
            (pre-f v0 v1 v2 v3 v4 ) 
            (inv-f v0 v1 v2 v3 v4 )
        ))


        (not (=>
            (and 
                (inv-f v0 v1 v2 v3 v4 )
                (trans-f v0 v1 v2 v3 v4  v0! v1! v2! v3! v4! )
            )
            (inv-f v0! v1! v2! v3! v4! )
        ))


        (not (=> 
            (inv-f v0 v1 v2 v3 v4 ) 
            (post-f v0 v1 v2 v3 v4 )
        ))
    )
)

(check-sat)
                