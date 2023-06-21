(set-logic LIA)

(define-fun inv-f ((i Int) (j Int) (conf_0 Int) (x Int) (y Int) (i_0 Int) (i_1 Int) (j_0 Int) (j_1 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (x_0 Int) (x_1 Int) (x_2 Int) (y_0 Int) (y_1 Int) (y_2 Int)) Bool (and (or (not (= i i_1)) (not (= j j_1)) (not (= conf_0 conf_0_1)) (not (= x x_1)) (not (= y y_1)) (not (not (= x_1 0))) (not (= y_1 0)) (not (not (= i_1 j_1)))) (<= x 1) (<= y 1)))



(define-fun pre-f ((i Int) (j Int) (conf_0 Int) (x Int) (y Int) (i_0 Int) (i_1 Int) (j_0 Int) (j_1 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (x_0 Int) (x_1 Int) (x_2 Int) (y_0 Int) (y_1 Int) (y_2 Int)) Bool

    (and (= i i_1) (= j j_1) (= conf_0 conf_0_0) (= x x_0) (= y y_0) (= conf_0_0 1) (= i_1 x_0) (= j_1 y_0)))

(define-fun trans-f ((i Int) (j Int) (conf_0 Int) (x Int) (y Int) (i_0 Int) (i_1 Int) (j_0 Int) (j_1 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (x_0 Int) (x_1 Int) (x_2 Int) (y_0 Int) (y_1 Int) (y_2 Int) (i! Int) (j! Int) (conf_0! Int) (x! Int) (y! Int) (i_0! Int) (i_1! Int) (j_0! Int) (j_1! Int) (conf_0_0! Int) (conf_0_1! Int) (conf_0_2! Int) (conf_0_3! Int) (x_0! Int) (x_1! Int) (x_2! Int) (y_0! Int) (y_1! Int) (y_2! Int)) Bool

    (or (and (= conf_0_1 conf_0) (= x_1 x) (= y_1 y) (= conf_0_1 conf_0!) (= x_1 x!) (= y_1 y!) (= i i!) (= j j!) (= conf_0 conf_0!) (= y y!)) (and (= conf_0_1 conf_0) (= x_1 x) (= y_1 y) (not (= x_1 0)) (= x_2 (- x_1 1)) (= conf_0_2 (+ conf_0_1 827)) (= y_2 (- y_1 1)) (= conf_0_3 (- conf_0_2 224)) (= conf_0_3 conf_0!) (= x_2 x!) (= y_2 y!) (= i i_1) (= i! i_1) (= j j_1) (= j! j_1))))

(define-fun post-f ((i Int) (j Int) (conf_0 Int) (x Int) (y Int) (i_0 Int) (i_1 Int) (j_0 Int) (j_1 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (x_0 Int) (x_1 Int) (x_2 Int) (y_0 Int) (y_1 Int) (y_2 Int)) Bool

    (or (not (and (= i i_1) (= j j_1) (= conf_0 conf_0_1) (= x x_1) (= y y_1))) (not (and (not (not (= x_1 0))) (not (= y_1 0)) (not (not (= i_1 j_1)))))))





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
(declare-const v15 Int)
(declare-const v15! Int)
(declare-const v16 Int)
(declare-const v16! Int)
(declare-const v17 Int)
(declare-const v17! Int)
(declare-const v18 Int)
(declare-const v18! Int)

(assert
    (or
        (not (=> 
            (pre-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 ) 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 )
        ))


        (not (=>
            (and 
                (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 )
                (trans-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18  v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! v12! v13! v14! v15! v16! v17! v18! )
            )
            (inv-f v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! v12! v13! v14! v15! v16! v17! v18! )
        ))


        (not (=> 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 ) 
            (post-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 )
        ))
    )
)

(check-sat)
                