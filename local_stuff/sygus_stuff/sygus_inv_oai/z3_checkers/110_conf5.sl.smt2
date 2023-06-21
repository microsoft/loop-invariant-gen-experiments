(set-logic LIA)

(define-fun inv-f ((i Int) (conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (n Int) (sn Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (conf_0_0 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_2_1 Int) (conf_2_2 Int) (conf_3_0 Int) (conf_4_0 Int) (conf_4_1 Int) (conf_4_2 Int) (n_0 Int) (sn_0 Int) (sn_1 Int) (sn_2 Int) (sn_3 Int)) Bool (and (or (not (= i i_2)) (not (= conf_0 conf_0_0)) (not (= conf_1 conf_1_0)) (not (= conf_2 conf_2_1)) (not (= conf_3 conf_3_0)) (not (= conf_4 conf_4_1)) (not (= n n_0)) (not (= sn sn_2)) (<= i_2 n_0) (= sn_2 n_0) (= sn_2 0)) (<= sn n_0)))



(define-fun pre-f ((i Int) (conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (n Int) (sn Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (conf_0_0 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_2_1 Int) (conf_2_2 Int) (conf_3_0 Int) (conf_4_0 Int) (conf_4_1 Int) (conf_4_2 Int) (n_0 Int) (sn_0 Int) (sn_1 Int) (sn_2 Int) (sn_3 Int)) Bool

    (and (= i i_1) (= conf_0 conf_0_0) (= conf_1 conf_1_0) (= conf_2 conf_2_0) (= conf_3 conf_3_0) (= conf_4 conf_4_0) (= sn sn_1) (= conf_0_0 3) (= conf_1_0 2) (= conf_2_0 3) (= conf_3_0 2) (= conf_4_0 6) (= sn_1 0) (= i_1 1)))

(define-fun trans-f ((i Int) (conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (n Int) (sn Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (conf_0_0 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_2_1 Int) (conf_2_2 Int) (conf_3_0 Int) (conf_4_0 Int) (conf_4_1 Int) (conf_4_2 Int) (n_0 Int) (sn_0 Int) (sn_1 Int) (sn_2 Int) (sn_3 Int) (i! Int) (conf_0! Int) (conf_1! Int) (conf_2! Int) (conf_3! Int) (conf_4! Int) (n! Int) (sn! Int) (i_0! Int) (i_1! Int) (i_2! Int) (i_3! Int) (conf_0_0! Int) (conf_1_0! Int) (conf_2_0! Int) (conf_2_1! Int) (conf_2_2! Int) (conf_3_0! Int) (conf_4_0! Int) (conf_4_1! Int) (conf_4_2! Int) (n_0! Int) (sn_0! Int) (sn_1! Int) (sn_2! Int) (sn_3! Int)) Bool

    (or (and (= i_2 i) (= conf_2_1 conf_2) (= conf_4_1 conf_4) (= sn_2 sn) (= i_2 i!) (= conf_2_1 conf_2!) (= conf_4_1 conf_4!) (= sn_2 sn!) (= n n_0) (= n! n_0) (= conf_0 conf_0!) (= conf_1 conf_1!) (= conf_2 conf_2!) (= conf_3 conf_3!) (= conf_4 conf_4!) (= sn sn!)) (and (= i_2 i) (= conf_2_1 conf_2) (= conf_4_1 conf_4) (= sn_2 sn) (<= i_2 n_0) (= i_3 (+ i_2 1)) (= conf_4_2 conf_3_0) (= sn_3 (+ sn_2 1)) (= conf_2_2 639) (= i_3 i!) (= conf_2_2 conf_2!) (= conf_4_2 conf_4!) (= sn_3 sn!) (= conf_0 conf_0_0) (= conf_0! conf_0_0) (= conf_1 conf_1_0) (= conf_1! conf_1_0) (= conf_3 conf_3_0) (= conf_3! conf_3_0) (= n n_0) (= n! n_0))))

(define-fun post-f ((i Int) (conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (n Int) (sn Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (conf_0_0 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_2_1 Int) (conf_2_2 Int) (conf_3_0 Int) (conf_4_0 Int) (conf_4_1 Int) (conf_4_2 Int) (n_0 Int) (sn_0 Int) (sn_1 Int) (sn_2 Int) (sn_3 Int)) Bool

    (or (not (and (= i i_2) (= conf_0 conf_0_0) (= conf_1 conf_1_0) (= conf_2 conf_2_1) (= conf_3 conf_3_0) (= conf_4 conf_4_1) (= n n_0) (= sn sn_2))) (not (and (not (<= i_2 n_0)) (not (= sn_2 n_0)) (not (= sn_2 0))))))





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
                