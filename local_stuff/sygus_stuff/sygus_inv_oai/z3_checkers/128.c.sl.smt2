(set-logic LIA)

(define-fun inv-f ((x Int) (y Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int)) Bool (or (not (= x x_2)) (not (= y y_0)) (>= x_2 1) (>= x_2 y_0)))



(define-fun pre-f ((x Int) (y Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int)) Bool

    (and (= x x_1) (= x_1 1)))

(define-fun trans-f ((x Int) (y Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (x! Int) (y! Int) (x_0! Int) (x_1! Int) (x_2! Int) (x_3! Int) (y_0! Int)) Bool

    (or (and (= x_2 x) (= x_2 x!) (= y y_0) (= y! y_0)) (and (= x_2 x) (< x_2 y_0) (= x_3 (+ x_2 x_2)) (= x_3 x!) (= y y_0) (= y! y_0))))

(define-fun post-f ((x Int) (y Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int)) Bool

    (or (not (and (= x x_2) (= y y_0))) (not (and (not (< x_2 y_0)) (not (>= x_2 1))))))





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
(declare-const v6 Int)
(declare-const v6! Int)

(assert
    (or
        (not (=> 
            (pre-f v0 v1 v2 v3 v4 v5 v6 ) 
            (inv-f v0 v1 v2 v3 v4 v5 v6 )
        ))


        (not (=>
            (and 
                (inv-f v0 v1 v2 v3 v4 v5 v6 )
                (trans-f v0 v1 v2 v3 v4 v5 v6  v0! v1! v2! v3! v4! v5! v6! )
            )
            (inv-f v0! v1! v2! v3! v4! v5! v6! )
        ))


        (not (=> 
            (inv-f v0 v1 v2 v3 v4 v5 v6 ) 
            (post-f v0 v1 v2 v3 v4 v5 v6 )
        ))
    )
)

(check-sat)
                