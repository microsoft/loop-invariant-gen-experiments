(set-logic LIA)

(define-fun inv-f ((conf_0 Int) (x Int) (y Int) (tmp Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (x_0 Int) (x_1 Int) (x_2 Int) (y_0 Int) (y_1 Int) (y_2 Int)) Bool (and (or (not (= conf_0 conf_0_1)) (not (= x x_1)) (not (= y y_1)) (not (= y_1 0)) (not (= x_1 20))) (>= y 0)))



(define-fun pre-f ((conf_0 Int) (x Int) (y Int) (tmp Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (x_0 Int) (x_1 Int) (x_2 Int) (y_0 Int) (y_1 Int) (y_2 Int)) Bool

    (and (= conf_0 conf_0_0) (= x x_0) (= y y_0) (= conf_0_0 1) (>= x_0 0) (<= x_0 10) (<= y_0 10) (>= y_0 0)))

(define-fun trans-f ((conf_0 Int) (x Int) (y Int) (tmp Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (x_0 Int) (x_1 Int) (x_2 Int) (y_0 Int) (y_1 Int) (y_2 Int) (conf_0! Int) (x! Int) (y! Int) (tmp! Int) (conf_0_0! Int) (conf_0_1! Int) (conf_0_2! Int) (conf_0_3! Int) (x_0! Int) (x_1! Int) (x_2! Int) (y_0! Int) (y_1! Int) (y_2! Int)) Bool

    (or (and (= conf_0_1 conf_0) (= x_1 x) (= y_1 y) (= conf_0_1 conf_0!) (= x_1 x!) (= y_1 y!) (= conf_0 conf_0!) (= x x!) (= y y!) (= tmp tmp!)) (and (= conf_0_1 conf_0) (= x_1 x) (= y_1 y) (= x_2 (+ x_1 10)) (= conf_0_2 conf_0_1) (= y_2 (+ y_1 10)) (= conf_0_3 (+ conf_0_2 conf_0_2)) (= conf_0_3 conf_0!) (= x_2 x!) (= y_2 y!) (= tmp tmp!))))

(define-fun post-f ((conf_0 Int) (x Int) (y Int) (tmp Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (x_0 Int) (x_1 Int) (x_2 Int) (y_0 Int) (y_1 Int) (y_2 Int)) Bool

    (or (not (and (= conf_0 conf_0_1) (= x x_1) (= y y_1))) (not (and (= y_1 0) (not (not (= x_1 20)))))))





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
(declare-const v12 Int)
(declare-const v12! Int)
(declare-const v13 Int)
(declare-const v13! Int)

(assert
    (or
        (not (=> 
            (pre-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 ) 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 )
        ))


        (not (=>
            (and 
                (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 )
                (trans-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13  v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! v12! v13! )
            )
            (inv-f v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! v12! v13! )
        ))


        (not (=> 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 ) 
            (post-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 )
        ))
    )
)

(check-sat)
                