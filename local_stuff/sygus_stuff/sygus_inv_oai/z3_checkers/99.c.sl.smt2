(set-logic LIA)

(define-fun inv-f ((n Int) (x Int) (y Int) (n_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int)) Bool (and (or (not (= n n_0)) (not (= x x_2)) (not (= y y_2)) (not (>= x_2 1)) (>= (+ n_0 (* (- 1) y_2)) 1)) (<= x n)))



(define-fun pre-f ((n Int) (x Int) (y Int) (n_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int)) Bool

    (and (= n n_0) (= x x_1) (= y y_1) (>= n_0 0) (= x_1 n_0) (= y_1 0)))

(define-fun trans-f ((n Int) (x Int) (y Int) (n_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int) (n! Int) (x! Int) (y! Int) (n_0! Int) (x_0! Int) (x_1! Int) (x_2! Int) (x_3! Int) (y_0! Int) (y_1! Int) (y_2! Int) (y_3! Int)) Bool

    (or (and (= x_2 x) (= y_2 y) (= x_2 x!) (= y_2 y!) (= n n!) (= y y!)) (and (= x_2 x) (= y_2 y) (> x_2 0) (= y_3 (+ y_2 1)) (= x_3 (- x_2 1)) (= x_3 x!) (= y_3 y!) (= n n_0) (= n! n_0))))

(define-fun post-f ((n Int) (x Int) (y Int) (n_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int)) Bool

    (or (not (and (= n n_0) (= x x_2) (= y y_2))) (not (and (not (> x_2 0)) (not (= n_0 (+ x_2 y_2)))))))





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
(declare-const v11 Int)
(declare-const v11! Int)

(assert
    (or
        (not (=> 
            (pre-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 ) 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 )
        ))


        (not (=>
            (and 
                (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 )
                (trans-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11  v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! )
            )
            (inv-f v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! )
        ))


        (not (=> 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 ) 
            (post-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 )
        ))
    )
)

(check-sat)
                