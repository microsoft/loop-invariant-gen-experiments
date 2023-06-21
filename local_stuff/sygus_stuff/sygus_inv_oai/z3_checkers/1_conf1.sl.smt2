(set-logic LIA)

(define-fun inv-f ((conf_0 Int) (x Int) (y Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int)) Bool (and (or (not (= conf_0 conf_0_1)) (not (= x x_2)) (not (= y y_2)) (>= y_2 100000) (>= x_2 y_2)) (<= y 100000)))



(define-fun pre-f ((conf_0 Int) (x Int) (y Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int)) Bool

    (and (= conf_0 conf_0_0) (= x x_1) (= y y_1) (= conf_0_0 4) (= x_1 1) (= y_1 0)))

(define-fun trans-f ((conf_0 Int) (x Int) (y Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int) (conf_0! Int) (x! Int) (y! Int) (conf_0_0! Int) (conf_0_1! Int) (conf_0_2! Int) (conf_0_3! Int) (x_0! Int) (x_1! Int) (x_2! Int) (x_3! Int) (y_0! Int) (y_1! Int) (y_2! Int) (y_3! Int)) Bool

    (or (and (= conf_0_1 conf_0) (= x_2 x) (= y_2 y) (= conf_0_1 conf_0!) (= x_2 x!) (= y_2 y!) (= conf_0 conf_0!) (= x x!)) (and (= conf_0_1 conf_0) (= x_2 x) (= y_2 y) (< y_2 100000) (= x_3 (+ x_2 y_2)) (= conf_0_2 (- 469 conf_0_1)) (= y_3 (+ y_2 1)) (= conf_0_3 (+ 687 622)) (= conf_0_3 conf_0!) (= x_3 x!) (= y_3 y!))))

(define-fun post-f ((conf_0 Int) (x Int) (y Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int)) Bool

    (or (not (and (= conf_0 conf_0_1) (= x x_2) (= y y_2))) (not (and (not (< y_2 100000)) (not (>= x_2 y_2))))))





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
(declare-const v14 Int)
(declare-const v14! Int)

(assert
    (or
        (not (=> 
            (pre-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 ) 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 )
        ))


        (not (=>
            (and 
                (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 )
                (trans-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14  v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! v12! v13! v14! )
            )
            (inv-f v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! v12! v13! v14! )
        ))


        (not (=> 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 ) 
            (post-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 )
        ))
    )
)

(check-sat)
                