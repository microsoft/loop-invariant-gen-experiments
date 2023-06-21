(set-logic LIA)

(define-fun inv-f ((conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (sn Int) (x Int) (tmp Int) (conf_0_0 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_2_1 Int) (conf_2_2 Int) (conf_3_0 Int) (conf_3_1 Int) (conf_3_2 Int) (conf_4_0 Int) (sn_0 Int) (sn_1 Int) (sn_2 Int) (sn_3 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int)) Bool (and (or (not (= conf_0 conf_0_0)) (not (= conf_1 conf_1_0)) (not (= conf_2 conf_2_1)) (not (= conf_3 conf_3_1)) (not (= conf_4 conf_4_0)) (not (= sn sn_2)) (not (= x x_2)) (>= sn_2 0) (>= x_2 0)) (<= sn x)))



(define-fun pre-f ((conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (sn Int) (x Int) (tmp Int) (conf_0_0 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_2_1 Int) (conf_2_2 Int) (conf_3_0 Int) (conf_3_1 Int) (conf_3_2 Int) (conf_4_0 Int) (sn_0 Int) (sn_1 Int) (sn_2 Int) (sn_3 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int)) Bool

    (and (= conf_0 conf_0_0) (= conf_1 conf_1_0) (= conf_2 conf_2_0) (= conf_3 conf_3_0) (= conf_4 conf_4_0) (= sn sn_1) (= x x_1) (= conf_0_0 8) (= conf_1_0 3) (= conf_2_0 4) (= conf_3_0 4) (= conf_4_0 7) (= sn_1 0) (= x_1 0)))

(define-fun trans-f ((conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (sn Int) (x Int) (tmp Int) (conf_0_0 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_2_1 Int) (conf_2_2 Int) (conf_3_0 Int) (conf_3_1 Int) (conf_3_2 Int) (conf_4_0 Int) (sn_0 Int) (sn_1 Int) (sn_2 Int) (sn_3 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (conf_0! Int) (conf_1! Int) (conf_2! Int) (conf_3! Int) (conf_4! Int) (sn! Int) (x! Int) (tmp! Int) (conf_0_0! Int) (conf_1_0! Int) (conf_2_0! Int) (conf_2_1! Int) (conf_2_2! Int) (conf_3_0! Int) (conf_3_1! Int) (conf_3_2! Int) (conf_4_0! Int) (sn_0! Int) (sn_1! Int) (sn_2! Int) (sn_3! Int) (x_0! Int) (x_1! Int) (x_2! Int) (x_3! Int)) Bool

    (or (and (= conf_2_1 conf_2) (= conf_3_1 conf_3) (= sn_2 sn) (= x_2 x) (= conf_2_1 conf_2!) (= conf_3_1 conf_3!) (= sn_2 sn!) (= x_2 x!) (= conf_0 conf_0!) (= conf_1 conf_1!) (= conf_2 conf_2!) (= conf_3 conf_3!) (= conf_4 conf_4!) (= sn sn!) (= x x!) (= tmp tmp!)) (and (= conf_2_1 conf_2) (= conf_3_1 conf_3) (= sn_2 sn) (= x_2 x) (= x_3 (+ x_2 1)) (= conf_3_2 (+ conf_3_1 conf_0_0)) (= sn_3 (+ sn_2 1)) (= conf_2_2 858) (= conf_2_2 conf_2!) (= conf_3_2 conf_3!) (= sn_3 sn!) (= x_3 x!) (= conf_0 conf_0_0) (= conf_0! conf_0_0) (= conf_1 conf_1_0) (= conf_1! conf_1_0) (= conf_4 conf_4_0) (= conf_4! conf_4_0) (= tmp tmp!))))

(define-fun post-f ((conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (sn Int) (x Int) (tmp Int) (conf_0_0 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_2_1 Int) (conf_2_2 Int) (conf_3_0 Int) (conf_3_1 Int) (conf_3_2 Int) (conf_4_0 Int) (sn_0 Int) (sn_1 Int) (sn_2 Int) (sn_3 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int)) Bool

    (or (not (and (= conf_0 conf_0_0) (= conf_1 conf_1_0) (= conf_2 conf_2_1) (= conf_3 conf_3_1) (= conf_4 conf_4_0) (= sn sn_2) (= x x_2))) (not (and (not (= sn_2 (- 1))) (not (= sn_2 x_2))))))





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
                