(set-logic LIA)

(define-fun inv-f ((i Int) (conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (n Int) (x Int) (y Int) (tmp Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (conf_0_0 Int) (conf_1_0 Int) (conf_1_1 Int) (conf_1_2 Int) (conf_1_3 Int) (conf_1_4 Int) (conf_2_0 Int) (conf_2_1 Int) (conf_2_2 Int) (conf_2_3 Int) (conf_2_4 Int) (conf_2_5 Int) (conf_3_0 Int) (conf_4_0 Int) (n_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (x_4 Int) (x_5 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int) (y_4 Int) (y_5 Int)) Bool (and (or (not (= i i_2)) (not (= conf_0 conf_0_0)) (not (= conf_1 conf_1_1)) (not (= conf_2 conf_2_1)) (not (= conf_3 conf_3_0)) (not (= conf_4 conf_4_0)) (not (= n n_0)) (not (= x x_2)) (not (= y y_2)) (>= i_2 n_0) (not (= (* 3 n_0) (+ x_2 y_2)))) (<= i n)))



(define-fun pre-f ((i Int) (conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (n Int) (x Int) (y Int) (tmp Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (conf_0_0 Int) (conf_1_0 Int) (conf_1_1 Int) (conf_1_2 Int) (conf_1_3 Int) (conf_1_4 Int) (conf_2_0 Int) (conf_2_1 Int) (conf_2_2 Int) (conf_2_3 Int) (conf_2_4 Int) (conf_2_5 Int) (conf_3_0 Int) (conf_4_0 Int) (n_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (x_4 Int) (x_5 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int) (y_4 Int) (y_5 Int)) Bool

    (and (= i i_1) (= conf_0 conf_0_0) (= conf_1 conf_1_0) (= conf_2 conf_2_0) (= conf_3 conf_3_0) (= conf_4 conf_4_0) (= n n_0) (= x x_1) (= y y_1) (= conf_0_0 8) (= conf_1_0 8) (= conf_2_0 5) (= conf_3_0 3) (= conf_4_0 3) (>= n_0 0) (= i_1 0) (= x_1 0) (= y_1 0)))

(define-fun trans-f ((i Int) (conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (n Int) (x Int) (y Int) (tmp Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (conf_0_0 Int) (conf_1_0 Int) (conf_1_1 Int) (conf_1_2 Int) (conf_1_3 Int) (conf_1_4 Int) (conf_2_0 Int) (conf_2_1 Int) (conf_2_2 Int) (conf_2_3 Int) (conf_2_4 Int) (conf_2_5 Int) (conf_3_0 Int) (conf_4_0 Int) (n_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (x_4 Int) (x_5 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int) (y_4 Int) (y_5 Int) (i! Int) (conf_0! Int) (conf_1! Int) (conf_2! Int) (conf_3! Int) (conf_4! Int) (n! Int) (x! Int) (y! Int) (tmp! Int) (i_0! Int) (i_1! Int) (i_2! Int) (i_3! Int) (conf_0_0! Int) (conf_1_0! Int) (conf_1_1! Int) (conf_1_2! Int) (conf_1_3! Int) (conf_1_4! Int) (conf_2_0! Int) (conf_2_1! Int) (conf_2_2! Int) (conf_2_3! Int) (conf_2_4! Int) (conf_2_5! Int) (conf_3_0! Int) (conf_4_0! Int) (n_0! Int) (x_0! Int) (x_1! Int) (x_2! Int) (x_3! Int) (x_4! Int) (x_5! Int) (y_0! Int) (y_1! Int) (y_2! Int) (y_3! Int) (y_4! Int) (y_5! Int)) Bool

    (or (and (= i_2 i) (= conf_1_1 conf_1) (= conf_2_1 conf_2) (= x_2 x) (= y_2 y) (= i_2 i!) (= conf_1_1 conf_1!) (= conf_2_1 conf_2!) (= x_2 x!) (= y_2 y!) (= n n_0) (= n! n_0) (= conf_0 conf_0!) (= conf_1 conf_1!) (= conf_2 conf_2!) (= conf_3 conf_3!) (= conf_4 conf_4!) (= x x!) (= y y!) (= tmp tmp!)) (and (= i_2 i) (= conf_1_1 conf_1) (= conf_2_1 conf_2) (= x_2 x) (= y_2 y) (< i_2 n_0) (= i_3 (+ i_2 1)) (= conf_2_2 (- conf_4_0 conf_2_1)) (= x_3 (+ x_2 1)) (= conf_1_2 (+ conf_3_0 conf_1_1)) (= y_3 (+ y_2 2)) (= conf_2_3 918) (= conf_1_3 conf_1_2) (= conf_2_4 conf_2_3) (= x_4 x_3) (= y_4 y_3) (= i_3 i!) (= conf_1_3 conf_1!) (= conf_2_4 conf_2!) (= x_4 x!) (= y_4 y!) (= conf_0 conf_0_0) (= conf_0! conf_0_0) (= conf_3 conf_3_0) (= conf_3! conf_3_0) (= conf_4 conf_4_0) (= conf_4! conf_4_0) (= n n_0) (= n! n_0) (= tmp tmp!)) (and (= i_2 i) (= conf_1_1 conf_1) (= conf_2_1 conf_2) (= x_2 x) (= y_2 y) (< i_2 n_0) (= i_3 (+ i_2 1)) (= conf_2_2 (- conf_4_0 conf_2_1)) (= x_5 (+ x_2 2)) (= conf_1_4 (+ 607 185)) (= y_5 (+ y_2 1)) (= conf_2_5 773) (= conf_1_3 conf_1_4) (= conf_2_4 conf_2_5) (= x_4 x_5) (= y_4 y_5) (= i_3 i!) (= conf_1_3 conf_1!) (= conf_2_4 conf_2!) (= x_4 x!) (= y_4 y!) (= conf_0 conf_0_0) (= conf_0! conf_0_0) (= conf_3 conf_3_0) (= conf_3! conf_3_0) (= conf_4 conf_4_0) (= conf_4! conf_4_0) (= n n_0) (= n! n_0) (= tmp tmp!))))

(define-fun post-f ((i Int) (conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (n Int) (x Int) (y Int) (tmp Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (conf_0_0 Int) (conf_1_0 Int) (conf_1_1 Int) (conf_1_2 Int) (conf_1_3 Int) (conf_1_4 Int) (conf_2_0 Int) (conf_2_1 Int) (conf_2_2 Int) (conf_2_3 Int) (conf_2_4 Int) (conf_2_5 Int) (conf_3_0 Int) (conf_4_0 Int) (n_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (x_4 Int) (x_5 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int) (y_4 Int) (y_5 Int)) Bool

    (or (not (and (= i i_2) (= conf_0 conf_0_0) (= conf_1 conf_1_1) (= conf_2 conf_2_1) (= conf_3 conf_3_0) (= conf_4 conf_4_0) (= n n_0) (= x x_2) (= y y_2))) (not (and (not (< i_2 n_0)) (not (= (* 3 n_0) (+ x_2 y_2)))))))





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
(declare-const v29 Int)
(declare-const v29! Int)
(declare-const v30 Int)
(declare-const v30! Int)
(declare-const v31 Int)
(declare-const v31! Int)
(declare-const v32 Int)
(declare-const v32! Int)
(declare-const v33 Int)
(declare-const v33! Int)
(declare-const v34 Int)
(declare-const v34! Int)
(declare-const v35 Int)
(declare-const v35! Int)
(declare-const v36 Int)
(declare-const v36! Int)
(declare-const v37 Int)
(declare-const v37! Int)
(declare-const v38 Int)
(declare-const v38! Int)
(declare-const v39 Int)
(declare-const v39! Int)
(declare-const v40 Int)
(declare-const v40! Int)

(assert
    (or
        (not (=> 
            (pre-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 ) 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 )
        ))


        (not (=>
            (and 
                (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 )
                (trans-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40  v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! v12! v13! v14! v15! v16! v17! v18! v19! v20! v21! v22! v23! v24! v25! v26! v27! v28! v29! v30! v31! v32! v33! v34! v35! v36! v37! v38! v39! v40! )
            )
            (inv-f v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! v12! v13! v14! v15! v16! v17! v18! v19! v20! v21! v22! v23! v24! v25! v26! v27! v28! v29! v30! v31! v32! v33! v34! v35! v36! v37! v38! v39! v40! )
        ))


        (not (=> 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 ) 
            (post-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 )
        ))
    )
)

(check-sat)
                