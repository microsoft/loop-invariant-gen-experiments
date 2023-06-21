(set-logic LIA)

(define-fun inv-f ((c Int) (conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (tmp Int) (c_0 Int) (c_1 Int) (c_2 Int) (c_3 Int) (c_4 Int) (c_5 Int) (conf_0_0 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_3_0 Int) (conf_3_1 Int) (conf_3_2 Int) (conf_3_3 Int) (conf_4_0 Int) (conf_4_1 Int) (conf_4_2 Int) (conf_4_3 Int)) Bool (and (or (not (= c c_2)) (not (= conf_0 conf_0_0)) (not (= conf_1 conf_1_0)) (not (= conf_2 conf_2_0)) (not (= conf_3 conf_3_1)) (not (= conf_4 conf_4_1)) (<= c_2 40)) (<= c 40)))



(define-fun pre-f ((c Int) (conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (tmp Int) (c_0 Int) (c_1 Int) (c_2 Int) (c_3 Int) (c_4 Int) (c_5 Int) (conf_0_0 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_3_0 Int) (conf_3_1 Int) (conf_3_2 Int) (conf_3_3 Int) (conf_4_0 Int) (conf_4_1 Int) (conf_4_2 Int) (conf_4_3 Int)) Bool

    (and (= c c_1) (= conf_0 conf_0_0) (= conf_1 conf_1_0) (= conf_2 conf_2_0) (= conf_3 conf_3_0) (= conf_4 conf_4_0) (= conf_0_0 6) (= conf_1_0 8) (= conf_2_0 6) (= conf_3_0 6) (= conf_4_0 4) (= c_1 0)))

(define-fun trans-f ((c Int) (conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (tmp Int) (c_0 Int) (c_1 Int) (c_2 Int) (c_3 Int) (c_4 Int) (c_5 Int) (conf_0_0 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_3_0 Int) (conf_3_1 Int) (conf_3_2 Int) (conf_3_3 Int) (conf_4_0 Int) (conf_4_1 Int) (conf_4_2 Int) (conf_4_3 Int) (c! Int) (conf_0! Int) (conf_1! Int) (conf_2! Int) (conf_3! Int) (conf_4! Int) (tmp! Int) (c_0! Int) (c_1! Int) (c_2! Int) (c_3! Int) (c_4! Int) (c_5! Int) (conf_0_0! Int) (conf_1_0! Int) (conf_2_0! Int) (conf_3_0! Int) (conf_3_1! Int) (conf_3_2! Int) (conf_3_3! Int) (conf_4_0! Int) (conf_4_1! Int) (conf_4_2! Int) (conf_4_3! Int)) Bool

    (or (and (= c_2 c) (= conf_3_1 conf_3) (= conf_4_1 conf_4) (= c_2 c!) (= conf_3_1 conf_3!) (= conf_4_1 conf_4!) (= c c!) (= conf_0 conf_0!) (= conf_1 conf_1!) (= conf_2 conf_2!) (= conf_3 conf_3!) (= conf_4 conf_4!) (= tmp tmp!)) (and (= c_2 c) (= conf_3_1 conf_3) (= conf_4_1 conf_4) (not (= c_2 40)) (= c_3 (+ c_2 1)) (= conf_3_2 317) (= c_4 c_3) (= conf_3_3 conf_3_2) (= conf_4_2 conf_4_1) (= c_4 c!) (= conf_3_3 conf_3!) (= conf_4_2 conf_4!) (= conf_0 conf_0_0) (= conf_0! conf_0_0) (= conf_1 conf_1_0) (= conf_1! conf_1_0) (= conf_2 conf_2_0) (= conf_2! conf_2_0) (= tmp tmp!)) (and (= c_2 c) (= conf_3_1 conf_3) (= conf_4_1 conf_4) (not (not (= c_2 40))) (= c_4 c_2) (= conf_3_3 conf_3_1) (= conf_4_2 conf_4_1) (= c_4 c!) (= conf_3_3 conf_3!) (= conf_4_2 conf_4!) (= conf_0 conf_0_0) (= conf_0! conf_0_0) (= conf_1 conf_1_0) (= conf_1! conf_1_0) (= conf_2 conf_2_0) (= conf_2! conf_2_0) (= tmp tmp!)) (and (= c_2 c) (= conf_3_1 conf_3) (= conf_4_1 conf_4) (= c_2 40) (= c_5 1) (= conf_4_3 conf_0_0) (= c_4 c_5) (= conf_3_3 conf_3_1) (= conf_4_2 conf_4_3) (= c_4 c!) (= conf_3_3 conf_3!) (= conf_4_2 conf_4!) (= conf_0 conf_0_0) (= conf_0! conf_0_0) (= conf_1 conf_1_0) (= conf_1! conf_1_0) (= conf_2 conf_2_0) (= conf_2! conf_2_0) (= tmp tmp!)) (and (= c_2 c) (= conf_3_1 conf_3) (= conf_4_1 conf_4) (not (= c_2 40)) (= c_4 c_2) (= conf_3_3 conf_3_1) (= conf_4_2 conf_4_1) (= c_4 c!) (= conf_3_3 conf_3!) (= conf_4_2 conf_4!) (= conf_0 conf_0_0) (= conf_0! conf_0_0) (= conf_1 conf_1_0) (= conf_1! conf_1_0) (= conf_2 conf_2_0) (= conf_2! conf_2_0) (= tmp tmp!))))

(define-fun post-f ((c Int) (conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (tmp Int) (c_0 Int) (c_1 Int) (c_2 Int) (c_3 Int) (c_4 Int) (c_5 Int) (conf_0_0 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_3_0 Int) (conf_3_1 Int) (conf_3_2 Int) (conf_3_3 Int) (conf_4_0 Int) (conf_4_1 Int) (conf_4_2 Int) (conf_4_3 Int)) Bool

    (or (not (and (= c c_2) (= conf_0 conf_0_0) (= conf_1 conf_1_0) (= conf_2 conf_2_0) (= conf_3 conf_3_1) (= conf_4 conf_4_1))) (not (and (not (= c_2 40)) (not (<= c_2 40))))))





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

(assert
    (or
        (not (=> 
            (pre-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 ) 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 )
        ))


        (not (=>
            (and 
                (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 )
                (trans-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23  v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! v12! v13! v14! v15! v16! v17! v18! v19! v20! v21! v22! v23! )
            )
            (inv-f v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! v12! v13! v14! v15! v16! v17! v18! v19! v20! v21! v22! v23! )
        ))


        (not (=> 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 ) 
            (post-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 )
        ))
    )
)

(check-sat)
                