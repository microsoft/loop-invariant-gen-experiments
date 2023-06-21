(set-logic LIA)

(define-fun inv-f ((x Int) (y Int) (x_0 Int) (y_0 Int) (y_1 Int) (y_2 Int)) Bool (>= y 0))



(define-fun pre-f ((x Int) (y Int) (x_0 Int) (y_0 Int) (y_1 Int) (y_2 Int)) Bool

    (and (= x x_0) (= y y_0) (= x_0 0) (= y_0 0)))

(define-fun trans-f ((x Int) (y Int) (x_0 Int) (y_0 Int) (y_1 Int) (y_2 Int) (x! Int) (y! Int) (x_0! Int) (y_0! Int) (y_1! Int) (y_2! Int)) Bool

    (or (and (= y_1 y) (= y_1 y!) (= x x!)) (and (= y_1 y) (>= y_1 0) (= y_2 (+ y_1 x_0)) (= y_2 y!) (= x x_0) (= x! x_0))))

(define-fun post-f ((x Int) (y Int) (x_0 Int) (y_0 Int) (y_1 Int) (y_2 Int)) Bool

    (or (not (and (= x x_0) (= y y_1))) (not (and (not (>= y_1 0)) (not (>= y_1 0))))))





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
(declare-const v5 Int)
(declare-const v5! Int)

(assert
    (or
        (not (=> 
            (pre-f v0 v1 v2 v3 v4 v5 ) 
            (inv-f v0 v1 v2 v3 v4 v5 )
        ))


        (not (=>
            (and 
                (inv-f v0 v1 v2 v3 v4 v5 )
                (trans-f v0 v1 v2 v3 v4 v5  v0! v1! v2! v3! v4! v5! )
            )
            (inv-f v0! v1! v2! v3! v4! v5! )
        ))


        (not (=> 
            (inv-f v0 v1 v2 v3 v4 v5 ) 
            (post-f v0 v1 v2 v3 v4 v5 )
        ))
    )
)

(check-sat)
                