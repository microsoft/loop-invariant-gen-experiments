(set-logic LIA)

(define-fun inv-f ((conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (lock Int) (x Int) (y Int) (tmp Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (conf_1_0 Int) (conf_1_1 Int) (conf_1_2 Int) (conf_1_3 Int) (conf_2_0 Int) (conf_3_0 Int) (conf_3_1 Int) (conf_3_2 Int) (conf_3_3 Int) (conf_4_0 Int) (conf_4_1 Int) (conf_4_2 Int) (conf_4_3 Int) (lock_0 Int) (lock_1 Int) (lock_2 Int) (lock_3 Int) (lock_4 Int) (lock_5 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (x_4 Int) (x_5 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int)) Bool (and (or (not (= conf_0 conf_0_1)) (not (= conf_1 conf_1_1)) (not (= conf_2 conf_2_0)) (not (= conf_3 conf_3_1)) (not (= conf_4 conf_4_1)) (not (= lock lock_2)) (not (= x x_2)) (not (= y y_1)) (not (= x_2 y_1)) (not (= lock_2 1))) (<= lock 1)))



(define-fun pre-f ((conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (lock Int) (x Int) (y Int) (tmp Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (conf_1_0 Int) (conf_1_1 Int) (conf_1_2 Int) (conf_1_3 Int) (conf_2_0 Int) (conf_3_0 Int) (conf_3_1 Int) (conf_3_2 Int) (conf_3_3 Int) (conf_4_0 Int) (conf_4_1 Int) (conf_4_2 Int) (conf_4_3 Int) (lock_0 Int) (lock_1 Int) (lock_2 Int) (lock_3 Int) (lock_4 Int) (lock_5 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (x_4 Int) (x_5 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int)) Bool

    (and (= conf_0 conf_0_0) (= conf_1 conf_1_0) (= conf_2 conf_2_0) (= conf_3 conf_3_0) (= conf_4 conf_4_0) (= lock lock_1) (= x x_1) (= y y_0) (= conf_0_0 8) (= conf_1_0 3) (= conf_2_0 2) (= conf_3_0 7) (= conf_4_0 5) (= x_1 y_0) (= lock_1 1)))

(define-fun trans-f ((conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (lock Int) (x Int) (y Int) (tmp Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (conf_1_0 Int) (conf_1_1 Int) (conf_1_2 Int) (conf_1_3 Int) (conf_2_0 Int) (conf_3_0 Int) (conf_3_1 Int) (conf_3_2 Int) (conf_3_3 Int) (conf_4_0 Int) (conf_4_1 Int) (conf_4_2 Int) (conf_4_3 Int) (lock_0 Int) (lock_1 Int) (lock_2 Int) (lock_3 Int) (lock_4 Int) (lock_5 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (x_4 Int) (x_5 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int) (conf_0! Int) (conf_1! Int) (conf_2! Int) (conf_3! Int) (conf_4! Int) (lock! Int) (x! Int) (y! Int) (tmp! Int) (conf_0_0! Int) (conf_0_1! Int) (conf_0_2! Int) (conf_0_3! Int) (conf_0_4! Int) (conf_1_0! Int) (conf_1_1! Int) (conf_1_2! Int) (conf_1_3! Int) (conf_2_0! Int) (conf_3_0! Int) (conf_3_1! Int) (conf_3_2! Int) (conf_3_3! Int) (conf_4_0! Int) (conf_4_1! Int) (conf_4_2! Int) (conf_4_3! Int) (lock_0! Int) (lock_1! Int) (lock_2! Int) (lock_3! Int) (lock_4! Int) (lock_5! Int) (x_0! Int) (x_1! Int) (x_2! Int) (x_3! Int) (x_4! Int) (x_5! Int) (y_0! Int) (y_1! Int) (y_2! Int) (y_3! Int)) Bool

    (or (and (= conf_0_1 conf_0) (= conf_1_1 conf_1) (= conf_3_1 conf_3) (= conf_4_1 conf_4) (= lock_2 lock) (= x_2 x) (= y_1 y) (= conf_0_1 conf_0!) (= conf_1_1 conf_1!) (= conf_3_1 conf_3!) (= conf_4_1 conf_4!) (= lock_2 lock!) (= x_2 x!) (= y_1 y!) (= conf_0 conf_0!) (= conf_1 conf_1!) (= conf_2 conf_2!) (= conf_3 conf_3!) (= conf_4 conf_4!) (= lock lock!) (= tmp tmp!)) (and (= conf_0_1 conf_0) (= conf_1_1 conf_1) (= conf_3_1 conf_3) (= conf_4_1 conf_4) (= lock_2 lock) (= x_2 x) (= y_1 y) (not (= x_2 y_1)) (= lock_3 1) (= conf_3_2 (+ 445 35)) (= x_3 y_1) (= conf_1_2 (- conf_4_1 303)) (= conf_0_2 conf_0_1) (= conf_1_3 conf_1_2) (= conf_3_3 conf_3_2) (= conf_4_2 conf_4_1) (= lock_4 lock_3) (= x_4 x_3) (= y_2 y_1) (= conf_0_2 conf_0!) (= conf_1_3 conf_1!) (= conf_3_3 conf_3!) (= conf_4_2 conf_4!) (= lock_4 lock!) (= x_4 x!) (= y_2 y!) (= conf_2 conf_2_0) (= conf_2! conf_2_0) (= tmp tmp!)) (and (= conf_0_1 conf_0) (= conf_1_1 conf_1) (= conf_3_1 conf_3) (= conf_4_1 conf_4) (= lock_2 lock) (= x_2 x) (= y_1 y) (not (= x_2 y_1)) (= lock_5 0) (= conf_0_3 (- conf_3_1 403)) (= x_5 y_1) (= conf_0_4 73) (= y_3 (+ y_1 1)) (= conf_4_3 (+ 587 conf_3_1)) (= conf_0_2 conf_0_4) (= conf_1_3 conf_1_1) (= conf_3_3 conf_3_1) (= conf_4_2 conf_4_3) (= lock_4 lock_5) (= x_4 x_5) (= y_2 y_3) (= conf_0_2 conf_0!) (= conf_1_3 conf_1!) (= conf_3_3 conf_3!) (= conf_4_2 conf_4!) (= lock_4 lock!) (= x_4 x!) (= y_2 y!) (= conf_2 conf_2_0) (= conf_2! conf_2_0) (= tmp tmp!))))

(define-fun post-f ((conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (lock Int) (x Int) (y Int) (tmp Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (conf_1_0 Int) (conf_1_1 Int) (conf_1_2 Int) (conf_1_3 Int) (conf_2_0 Int) (conf_3_0 Int) (conf_3_1 Int) (conf_3_2 Int) (conf_3_3 Int) (conf_4_0 Int) (conf_4_1 Int) (conf_4_2 Int) (conf_4_3 Int) (lock_0 Int) (lock_1 Int) (lock_2 Int) (lock_3 Int) (lock_4 Int) (lock_5 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (x_4 Int) (x_5 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int)) Bool

    (or (not (and (= conf_0 conf_0_1) (= conf_1 conf_1_1) (= conf_2 conf_2_0) (= conf_3 conf_3_1) (= conf_4 conf_4_1) (= lock lock_2) (= x x_2) (= y y_1))) (not (and (not (not (= x_2 y_1))) (not (= lock_2 1))))))





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
(declare-const v41 Int)
(declare-const v41! Int)
(declare-const v42 Int)
(declare-const v42! Int)

(assert
    (or
        (not (=> 
            (pre-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 ) 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 )
        ))


        (not (=>
            (and 
                (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 )
                (trans-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42  v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! v12! v13! v14! v15! v16! v17! v18! v19! v20! v21! v22! v23! v24! v25! v26! v27! v28! v29! v30! v31! v32! v33! v34! v35! v36! v37! v38! v39! v40! v41! v42! )
            )
            (inv-f v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! v12! v13! v14! v15! v16! v17! v18! v19! v20! v21! v22! v23! v24! v25! v26! v27! v28! v29! v30! v31! v32! v33! v34! v35! v36! v37! v38! v39! v40! v41! v42! )
        ))


        (not (=> 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 ) 
            (post-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 )
        ))
    )
)

(check-sat)
                