(set-logic LIA)

(define-fun inv-f ((c Int) (conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (y Int) (z Int) (tmp Int) (c_0 Int) (c_1 Int) (c_2 Int) (c_3 Int) (c_4 Int) (conf_0_0 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_3_0 Int) (conf_3_1 Int) (conf_3_2 Int) (conf_3_3 Int) (conf_3_4 Int) (conf_4_0 Int) (y_0 Int) (z_0 Int) (z_1 Int) (z_2 Int) (z_3 Int) (z_4 Int)) Bool (and (or (not (= c c_2)) (not (= conf_0 conf_0_0)) (not (= conf_1 conf_1_0)) (not (= conf_2 conf_2_0)) (not (= conf_3 conf_3_1)) (not (= conf_4 conf_4_0)) (not (= y y_0)) (not (= z z_2)) (>= c_2 36) (>= z_2 0)) (<= c 36)))



(define-fun pre-f ((c Int) (conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (y Int) (z Int) (tmp Int) (c_0 Int) (c_1 Int) (c_2 Int) (c_3 Int) (c_4 Int) (conf_0_0 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_3_0 Int) (conf_3_1 Int) (conf_3_2 Int) (conf_3_3 Int) (conf_3_4 Int) (conf_4_0 Int) (y_0 Int) (z_0 Int) (z_1 Int) (z_2 Int) (z_3 Int) (z_4 Int)) Bool

    (and (= c c_1) (= conf_0 conf_0_0) (= conf_1 conf_1_0) (= conf_2 conf_2_0) (= conf_3 conf_3_0) (= conf_4 conf_4_0) (= y y_0) (= z z_1) (= conf_0_0 6) (= conf_1_0 0) (= conf_2_0 3) (= conf_3_0 7) (= conf_4_0 6) (= c_1 0) (>= y_0 0) (>= y_0 127) (= z_1 (* 36 y_0))))

(define-fun trans-f ((c Int) (conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (y Int) (z Int) (tmp Int) (c_0 Int) (c_1 Int) (c_2 Int) (c_3 Int) (c_4 Int) (conf_0_0 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_3_0 Int) (conf_3_1 Int) (conf_3_2 Int) (conf_3_3 Int) (conf_3_4 Int) (conf_4_0 Int) (y_0 Int) (z_0 Int) (z_1 Int) (z_2 Int) (z_3 Int) (z_4 Int) (c! Int) (conf_0! Int) (conf_1! Int) (conf_2! Int) (conf_3! Int) (conf_4! Int) (y! Int) (z! Int) (tmp! Int) (c_0! Int) (c_1! Int) (c_2! Int) (c_3! Int) (c_4! Int) (conf_0_0! Int) (conf_1_0! Int) (conf_2_0! Int) (conf_3_0! Int) (conf_3_1! Int) (conf_3_2! Int) (conf_3_3! Int) (conf_3_4! Int) (conf_4_0! Int) (y_0! Int) (z_0! Int) (z_1! Int) (z_2! Int) (z_3! Int) (z_4! Int)) Bool

    (or (and (= c_2 c) (= conf_3_1 conf_3) (= z_2 z) (= c_2 c!) (= conf_3_1 conf_3!) (= z_2 z!) (= c c!) (= conf_0 conf_0!) (= conf_1 conf_1!) (= conf_2 conf_2!) (= conf_3 conf_3!) (= conf_4 conf_4!) (= y y!) (= z z!) (= tmp tmp!)) (and (= c_2 c) (= conf_3_1 conf_3) (= z_2 z) (< c_2 36) (= z_3 (+ z_2 1)) (= conf_3_2 conf_0_0) (= c_3 (+ c_2 1)) (= conf_3_3 conf_2_0) (= c_4 c_3) (= conf_3_4 conf_3_3) (= z_4 z_3) (= c_4 c!) (= conf_3_4 conf_3!) (= z_4 z!) (= conf_0 conf_0_0) (= conf_0! conf_0_0) (= conf_1 conf_1_0) (= conf_1! conf_1_0) (= conf_2 conf_2_0) (= conf_2! conf_2_0) (= conf_4 conf_4_0) (= conf_4! conf_4_0) (= y y_0) (= y! y_0) (= tmp tmp!)) (and (= c_2 c) (= conf_3_1 conf_3) (= z_2 z) (not (< c_2 36)) (= c_4 c_2) (= conf_3_4 conf_3_1) (= z_4 z_2) (= c_4 c!) (= conf_3_4 conf_3!) (= z_4 z!) (= conf_0 conf_0_0) (= conf_0! conf_0_0) (= conf_1 conf_1_0) (= conf_1! conf_1_0) (= conf_2 conf_2_0) (= conf_2! conf_2_0) (= conf_4 conf_4_0) (= conf_4! conf_4_0) (= y y_0) (= y! y_0) (= tmp tmp!))))

(define-fun post-f ((c Int) (conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (y Int) (z Int) (tmp Int) (c_0 Int) (c_1 Int) (c_2 Int) (c_3 Int) (c_4 Int) (conf_0_0 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_3_0 Int) (conf_3_1 Int) (conf_3_2 Int) (conf_3_3 Int) (conf_3_4 Int) (conf_4_0 Int) (y_0 Int) (z_0 Int) (z_1 Int) (z_2 Int) (z_3 Int) (z_4 Int)) Bool

    (or (not (and (= c c_2) (= conf_0 conf_0_0) (= conf_1 conf_1_0) (= conf_2 conf_2_0) (= conf_3 conf_3_1) (= conf_4 conf_4_0) (= y y_0) (= z z_2))) (not (and (< c_2 36) (not (>= z_2 0))))))





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
(declare-const v26 Int)
(declare-const v26! Int)
(declare-const v27 Int)
(declare-const v27! Int)
(declare-const v28 Int)
(declare-const v28! Int)

(assert
    (or
        (not (=> 
            (pre-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 ) 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 )
        ))


        (not (=>
            (and 
                (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 )
                (trans-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28  v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! v12! v13! v14! v15! v16! v17! v18! v19! v20! v21! v22! v23! v24! v25! v26! v27! v28! )
            )
            (inv-f v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! v12! v13! v14! v15! v16! v17! v18! v19! v20! v21! v22! v23! v24! v25! v26! v27! v28! )
        ))


        (not (=> 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 ) 
            (post-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 )
        ))
    )
)

(check-sat)
                