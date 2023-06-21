(set-logic LIA)

(define-fun inv-f ((conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (n Int) (x Int) (y Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_2_1 Int) (conf_2_2 Int) (conf_3_0 Int) (conf_4_0 Int) (n_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int)) Bool (and (or (not (= conf_0 conf_0_1)) (not (= conf_1 conf_1_0)) (not (= conf_2 conf_2_1)) (not (= conf_3 conf_3_0)) (not (= conf_4 conf_4_0)) (not (= n n_0)) (not (= x x_2)) (not (= y y_1)) (<= x_2 n_0) (not (> n_0 0)) (<= y_1 n_0)) (<= x 100000)))



(define-fun pre-f ((conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (n Int) (x Int) (y Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_2_1 Int) (conf_2_2 Int) (conf_3_0 Int) (conf_4_0 Int) (n_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int)) Bool

    (and (= conf_0 conf_0_0) (= conf_1 conf_1_0) (= conf_2 conf_2_0) (= conf_3 conf_3_0) (= conf_4 conf_4_0) (= x x_1) (= conf_0_0 2) (= conf_1_0 1) (= conf_2_0 2) (= conf_3_0 7) (= conf_4_0 8) (= x_1 1)))

(define-fun trans-f ((conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (n Int) (x Int) (y Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_2_1 Int) (conf_2_2 Int) (conf_3_0 Int) (conf_4_0 Int) (n_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int) (conf_0! Int) (conf_1! Int) (conf_2! Int) (conf_3! Int) (conf_4! Int) (n! Int) (x! Int) (y! Int) (conf_0_0! Int) (conf_0_1! Int) (conf_0_2! Int) (conf_1_0! Int) (conf_2_0! Int) (conf_2_1! Int) (conf_2_2! Int) (conf_3_0! Int) (conf_4_0! Int) (n_0! Int) (x_0! Int) (x_1! Int) (x_2! Int) (x_3! Int) (y_0! Int) (y_1! Int) (y_2! Int)) Bool

    (or (and (= conf_0_1 conf_0) (= conf_2_1 conf_2) (= x_2 x) (= y_1 y) (= conf_0_1 conf_0!) (= conf_2_1 conf_2!) (= x_2 x!) (= y_1 y!) (= n n_0) (= n! n_0) (= conf_0 conf_0!) (= conf_1 conf_1!) (= conf_2 conf_2!) (= conf_3 conf_3!) (= conf_4 conf_4!) (= y y!)) (and (= conf_0_1 conf_0) (= conf_2_1 conf_2) (= x_2 x) (= y_1 y) (<= x_2 n_0) (= y_2 (- n_0 x_2)) (= conf_0_2 (+ conf_4_0 292)) (= x_3 (+ x_2 1)) (= conf_2_2 conf_3_0) (= conf_0_2 conf_0!) (= conf_2_2 conf_2!) (= x_3 x!) (= y_2 y!) (= conf_1 conf_1_0) (= conf_1! conf_1_0) (= conf_3 conf_3_0) (= conf_3! conf_3_0) (= conf_4 conf_4_0) (= conf_4! conf_4_0) (= n n_0) (= n! n_0))))

(define-fun post-f ((conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (n Int) (x Int) (y Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_2_1 Int) (conf_2_2 Int) (conf_3_0 Int) (conf_4_0 Int) (n_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int)) Bool

    (or (not (and (= conf_0 conf_0_1) (= conf_1 conf_1_0) (= conf_2 conf_2_1) (= conf_3 conf_3_0) (= conf_4 conf_4_0) (= n n_0) (= x x_2) (= y y_1))) (not (and (not (<= x_2 n_0)) (> n_0 0) (not (<= y_1 n_0))))))





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
(declare-const v19 Int)
(declare-const v19! Int)
(declare-const v20 Int)
(declare-const v20! Int)
(declare-const v21 Int)
(declare-const v21! Int)
(declare-const v22 Int)
(declare-const v22! Int)
(declare-const v23 Int)
(declare-const v23! Int)
(declare-const v24 Int)
(declare-const v24! Int)

(assert
    (or
        (not (=> 
            (pre-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 ) 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 )
        ))


        (not (=>
            (and 
                (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 )
                (trans-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24  v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! v12! v13! v14! v15! v16! v17! v18! v19! v20! v21! v22! v23! v24! )
            )
            (inv-f v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! v12! v13! v14! v15! v16! v17! v18! v19! v20! v21! v22! v23! v24! )
        ))


        (not (=> 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 ) 
            (post-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 )
        ))
    )
)

(check-sat)
                