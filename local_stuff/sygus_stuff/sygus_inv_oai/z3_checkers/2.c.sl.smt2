(set-logic LIA)

(define-fun inv-f ((x Int) (y Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int)) Bool (and (or (not (= x x_2)) (not (= y y_2)) (>= y_2 1000) (>= x_2 y_2)) (<= y 1000)))



(define-fun pre-f ((x Int) (y Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int)) Bool

    (and (= x x_1) (= y y_1) (= x_1 1) (= y_1 0)))

(define-fun trans-f ((x Int) (y Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int) (x! Int) (y! Int) (x_0! Int) (x_1! Int) (x_2! Int) (x_3! Int) (y_0! Int) (y_1! Int) (y_2! Int) (y_3! Int)) Bool

    (or (and (= x_2 x) (= y_2 y) (= x_2 x!) (= y_2 y!) (= x x!)) (and (= x_2 x) (= y_2 y) (< y_2 1000) (= x_3 (+ x_2 y_2)) (= y_3 (+ y_2 1)) (= x_3 x!) (= y_3 y!))))

(define-fun post-f ((x Int) (y Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int)) Bool

    (or (not (and (= x x_2) (= y y_2))) (not (and (not (< y_2 1000)) (not (>= x_2 y_2))))))





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

(assert
    (or
        (not (=> 
            (pre-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 ) 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 )
        ))


        (not (=>
            (and 
                (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 )
                (trans-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9  v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! )
            )
            (inv-f v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! )
        ))


        (not (=> 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 ) 
            (post-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 )
        ))
    )
)

(check-sat)
                