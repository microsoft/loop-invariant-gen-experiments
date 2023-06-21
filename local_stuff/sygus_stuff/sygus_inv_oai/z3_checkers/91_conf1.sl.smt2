(set-logic LIA)

(define-fun inv-f ((conf_0 Int) (x Int) (y Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (x_0 Int) (x_1 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int)) Bool (and (or (not (= conf_0 conf_0_1)) (not (= x x_1)) (not (= y y_2)) (>= y_2 0)) (>= y 0)))



(define-fun pre-f ((conf_0 Int) (x Int) (y Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (x_0 Int) (x_1 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int)) Bool

    (and (= conf_0 conf_0_0) (= x x_1) (= y y_1) (= conf_0_0 8) (= x_1 0) (= y_1 0)))

(define-fun trans-f ((conf_0 Int) (x Int) (y Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (x_0 Int) (x_1 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int) (conf_0! Int) (x! Int) (y! Int) (conf_0_0! Int) (conf_0_1! Int) (conf_0_2! Int) (x_0! Int) (x_1! Int) (y_0! Int) (y_1! Int) (y_2! Int) (y_3! Int)) Bool

    (or (and (= conf_0_1 conf_0) (= y_2 y) (= conf_0_1 conf_0!) (= y_2 y!) (= conf_0 conf_0!) (= x x!)) (and (= conf_0_1 conf_0) (= y_2 y) (>= y_2 0) (= y_3 (+ y_2 x_1)) (= conf_0_2 conf_0_1) (= conf_0_2 conf_0!) (= y_3 y!) (= x x_1) (= x! x_1))))

(define-fun post-f ((conf_0 Int) (x Int) (y Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (x_0 Int) (x_1 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int)) Bool

    (or (not (and (= conf_0 conf_0_1) (= x x_1) (= y y_2))) (not (and (not (>= y_2 0)) (not (>= y_2 0))))))





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
                