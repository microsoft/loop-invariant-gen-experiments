(set-logic LIA)

(define-fun inv-f ((x Int) (y Int) (x_0 Int) (x_1 Int) (x_2 Int) (y_0 Int) (y_1 Int) (y_2 Int)) Bool (and (or (not (= x x_1)) (not (= y y_1)) (<= x_1 100) (>= y_1 100)) (<= x 101)))



(define-fun pre-f ((x Int) (y Int) (x_0 Int) (x_1 Int) (x_2 Int) (y_0 Int) (y_1 Int) (y_2 Int)) Bool

    (and (= x x_0) (= x_0 1)))

(define-fun trans-f ((x Int) (y Int) (x_0 Int) (x_1 Int) (x_2 Int) (y_0 Int) (y_1 Int) (y_2 Int) (x! Int) (y! Int) (x_0! Int) (x_1! Int) (x_2! Int) (y_0! Int) (y_1! Int) (y_2! Int)) Bool

    (or (and (= x_1 x) (= y_1 y) (= x_1 x!) (= y_1 y!) (= y y!)) (and (= x_1 x) (= y_1 y) (<= x_1 100) (= y_2 (- 100 x_1)) (= x_2 (+ x_1 1)) (= x_2 x!) (= y_2 y!))))

(define-fun post-f ((x Int) (y Int) (x_0 Int) (x_1 Int) (x_2 Int) (y_0 Int) (y_1 Int) (y_2 Int)) Bool

    (or (not (and (= x x_1) (= y y_1))) (not (and (not (<= x_1 100)) (not (< y_1 100))))))





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
(declare-const v7 Int)
(declare-const v7! Int)

(assert
    (or
        (not (=> 
            (pre-f v0 v1 v2 v3 v4 v5 v6 v7 ) 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 )
        ))


        (not (=>
            (and 
                (inv-f v0 v1 v2 v3 v4 v5 v6 v7 )
                (trans-f v0 v1 v2 v3 v4 v5 v6 v7  v0! v1! v2! v3! v4! v5! v6! v7! )
            )
            (inv-f v0! v1! v2! v3! v4! v5! v6! v7! )
        ))


        (not (=> 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 ) 
            (post-f v0 v1 v2 v3 v4 v5 v6 v7 )
        ))
    )
)

(check-sat)
                