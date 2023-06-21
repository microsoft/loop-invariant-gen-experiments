(set-logic LIA)

(define-fun inv-f ((c Int) (conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (n Int) (tmp Int) (c_0 Int) (c_1 Int) (c_2 Int) (c_3 Int) (c_4 Int) (c_5 Int) (conf_0_0 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_2_1 Int) (conf_2_2 Int) (conf_2_3 Int) (conf_3_0 Int) (conf_4_0 Int) (conf_4_1 Int) (conf_4_2 Int) (conf_4_3 Int) (n_0 Int)) Bool (and (or (not (= c c_2)) (not (= conf_0 conf_0_0)) (not (= conf_1 conf_1_0)) (not (= conf_2 conf_2_1)) (not (= conf_3 conf_3_0)) (not (= conf_4 conf_4_1)) (not (= n n_0)) (>= c_2 0)) (<= c n_0)))



(define-fun pre-f ((c Int) (conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (n Int) (tmp Int) (c_0 Int) (c_1 Int) (c_2 Int) (c_3 Int) (c_4 Int) (c_5 Int) (conf_0_0 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_2_1 Int) (conf_2_2 Int) (conf_2_3 Int) (conf_3_0 Int) (conf_4_0 Int) (conf_4_1 Int) (conf_4_2 Int) (conf_4_3 Int) (n_0 Int)) Bool

    (and (= c c_1) (= conf_0 conf_0_0) (= conf_1 conf_1_0) (= conf_2 conf_2_0) (= conf_3 conf_3_0) (= conf_4 conf_4_0) (= n n_0) (= conf_0_0 7) (= conf_1_0 1) (= conf_2_0 4) (= conf_3_0 5) (= conf_4_0 8) (= c_1 0) (> n_0 0)))

(define-fun trans-f ((c Int) (conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (n Int) (tmp Int) (c_0 Int) (c_1 Int) (c_2 Int) (c_3 Int) (c_4 Int) (c_5 Int) (conf_0_0 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_2_1 Int) (conf_2_2 Int) (conf_2_3 Int) (conf_3_0 Int) (conf_4_0 Int) (conf_4_1 Int) (conf_4_2 Int) (conf_4_3 Int) (n_0 Int) (c! Int) (conf_0! Int) (conf_1! Int) (conf_2! Int) (conf_3! Int) (conf_4! Int) (n! Int) (tmp! Int) (c_0! Int) (c_1! Int) (c_2! Int) (c_3! Int) (c_4! Int) (c_5! Int) (conf_0_0! Int) (conf_1_0! Int) (conf_2_0! Int) (conf_2_1! Int) (conf_2_2! Int) (conf_2_3! Int) (conf_3_0! Int) (conf_4_0! Int) (conf_4_1! Int) (conf_4_2! Int) (conf_4_3! Int) (n_0! Int)) Bool

    (or (and (= c_2 c) (= conf_2_1 conf_2) (= conf_4_1 conf_4) (= c_2 c!) (= conf_2_1 conf_2!) (= conf_4_1 conf_4!) (= c c!) (= conf_0 conf_0!) (= conf_1 conf_1!) (= conf_2 conf_2!) (= conf_3 conf_3!) (= conf_4 conf_4!) (= n n!) (= tmp tmp!)) (and (= c_2 c) (= conf_2_1 conf_2) (= conf_4_1 conf_4) (= c_2 n_0) (= c_3 1) (= conf_2_2 conf_3_0) (= c_4 c_3) (= conf_2_3 conf_2_2) (= conf_4_2 conf_4_1) (= c_4 c!) (= conf_2_3 conf_2!) (= conf_4_2 conf_4!) (= conf_0 conf_0_0) (= conf_0! conf_0_0) (= conf_1 conf_1_0) (= conf_1! conf_1_0) (= conf_3 conf_3_0) (= conf_3! conf_3_0) (= n n_0) (= n! n_0) (= tmp tmp!)) (and (= c_2 c) (= conf_2_1 conf_2) (= conf_4_1 conf_4) (not (= c_2 n_0)) (= c_5 (+ c_2 1)) (= conf_4_3 (- 947 94)) (= c_4 c_5) (= conf_2_3 conf_2_1) (= conf_4_2 conf_4_3) (= c_4 c!) (= conf_2_3 conf_2!) (= conf_4_2 conf_4!) (= conf_0 conf_0_0) (= conf_0! conf_0_0) (= conf_1 conf_1_0) (= conf_1! conf_1_0) (= conf_3 conf_3_0) (= conf_3! conf_3_0) (= n n_0) (= n! n_0) (= tmp tmp!))))

(define-fun post-f ((c Int) (conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (n Int) (tmp Int) (c_0 Int) (c_1 Int) (c_2 Int) (c_3 Int) (c_4 Int) (c_5 Int) (conf_0_0 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_2_1 Int) (conf_2_2 Int) (conf_2_3 Int) (conf_3_0 Int) (conf_4_0 Int) (conf_4_1 Int) (conf_4_2 Int) (conf_4_3 Int) (n_0 Int)) Bool

    (or (not (and (= c c_2) (= conf_0 conf_0_0) (= conf_1 conf_1_0) (= conf_2 conf_2_1) (= conf_3 conf_3_0) (= conf_4 conf_4_1) (= n n_0))) (not (and (= c_2 n_0) (not (>= c_2 0))))))





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
(declare-const v25 Int)
(declare-const v25! Int)

(assert
    (or
        (not (=> 
            (pre-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 ) 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 )
        ))


        (not (=>
            (and 
                (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 )
                (trans-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25  v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! v12! v13! v14! v15! v16! v17! v18! v19! v20! v21! v22! v23! v24! v25! )
            )
            (inv-f v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! v12! v13! v14! v15! v16! v17! v18! v19! v20! v21! v22! v23! v24! v25! )
        ))


        (not (=> 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 ) 
            (post-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 )
        ))
    )
)

(check-sat)
                