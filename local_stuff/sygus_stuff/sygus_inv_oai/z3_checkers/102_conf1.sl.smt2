(set-logic LIA)

(define-fun inv-f ((conf_0 Int) (n Int) (x Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (n_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int)) Bool (and (or (not (= conf_0 conf_0_1)) (not (= n n_0)) (not (= x x_2)) (>= x_2 n_0) (not (>= n_0 0)) (not (= x_2 n_0))) (<= x n_0)))



(define-fun pre-f ((conf_0 Int) (n Int) (x Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (n_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int)) Bool

    (and (= conf_0 conf_0_0) (= x x_1) (= conf_0_0 9) (= x_1 0)))

(define-fun trans-f ((conf_0 Int) (n Int) (x Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (n_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (conf_0! Int) (n! Int) (x! Int) (conf_0_0! Int) (conf_0_1! Int) (conf_0_2! Int) (n_0! Int) (x_0! Int) (x_1! Int) (x_2! Int) (x_3! Int)) Bool

    (or (and (= conf_0_1 conf_0) (= x_2 x) (= conf_0_1 conf_0!) (= x_2 x!) (= n n_0) (= n! n_0) (= conf_0 conf_0!)) (and (= conf_0_1 conf_0) (= x_2 x) (< x_2 n_0) (= x_3 (+ x_2 1)) (= conf_0_2 conf_0_1) (= conf_0_2 conf_0!) (= x_3 x!) (= n n_0) (= n! n_0))))

(define-fun post-f ((conf_0 Int) (n Int) (x Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (n_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int)) Bool

    (or (not (and (= conf_0 conf_0_1) (= n n_0) (= x x_2))) (not (and (not (< x_2 n_0)) (>= n_0 0) (not (= x_2 n_0))))))





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
                