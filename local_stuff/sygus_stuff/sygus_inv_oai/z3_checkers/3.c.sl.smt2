(set-logic LIA)

(define-fun inv-f ((x Int) (y Int) (z Int) (x_0 Int) (x_1 Int) (x_2 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int) (z_0 Int)) Bool (and (or (not (= x x_1)) (not (= y y_1)) (not (= z z_0)) (>= x_1 5) (>= z_0 y_1)) (<= x 5)))



(define-fun pre-f ((x Int) (y Int) (z Int) (x_0 Int) (x_1 Int) (x_2 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int) (z_0 Int)) Bool

    (and (= x x_0) (= x_0 0)))

(define-fun trans-f ((x Int) (y Int) (z Int) (x_0 Int) (x_1 Int) (x_2 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int) (z_0 Int) (x! Int) (y! Int) (z! Int) (x_0! Int) (x_1! Int) (x_2! Int) (y_0! Int) (y_1! Int) (y_2! Int) (y_3! Int) (z_0! Int)) Bool

    (or (and (= x_1 x) (= y_1 y) (= x_1 x!) (= y_1 y!) (= y y!) (= z z!)) (and (= x_1 x) (= y_1 y) (< x_1 5) (= x_2 (+ x_1 1)) (<= z_0 y_1) (= y_2 z_0) (= y_3 y_2) (= x_2 x!) (= y_3 y!) (= z z_0) (= z! z_0)) (and (= x_1 x) (= y_1 y) (< x_1 5) (= x_2 (+ x_1 1)) (not (<= z_0 y_1)) (= y_3 y_1) (= x_2 x!) (= y_3 y!) (= z z_0) (= z! z_0))))

(define-fun post-f ((x Int) (y Int) (z Int) (x_0 Int) (x_1 Int) (x_2 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int) (z_0 Int)) Bool

    (or (not (and (= x x_1) (= y y_1) (= z z_0))) (not (and (not (< x_1 5)) (not (>= z_0 y_1))))))





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
(declare-const v8 Int)
(declare-const v8! Int)
(declare-const v9 Int)
(declare-const v9! Int)
(declare-const v10 Int)
(declare-const v10! Int)

(assert
    (or
        (not (=> 
            (pre-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ) 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 )
        ))


        (not (=>
            (and 
                (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 )
                (trans-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10  v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! )
            )
            (inv-f v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! )
        ))


        (not (=> 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ) 
            (post-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 )
        ))
    )
)

(check-sat)
                