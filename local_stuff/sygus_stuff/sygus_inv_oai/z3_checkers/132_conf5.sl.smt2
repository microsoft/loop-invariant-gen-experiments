(set-logic LIA)

(define-fun inv-f ((c Int) (i Int) (j Int) (conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (t Int) (tmp Int) (c_0 Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (i_4 Int) (j_0 Int) (j_1 Int) (j_2 Int) (j_3 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_1_0 Int) (conf_1_1 Int) (conf_1_2 Int) (conf_1_3 Int) (conf_2_0 Int) (conf_3_0 Int) (conf_3_1 Int) (conf_3_2 Int) (conf_3_3 Int) (conf_4_0 Int) (t_0 Int) (t_1 Int) (t_2 Int) (t_3 Int)) Bool (and (or (not (= c c_0)) (not (= i i_2)) (not (= j j_1)) (not (= conf_0 conf_0_1)) (not (= conf_1 conf_1_1)) (not (= conf_2 conf_2_0)) (not (= conf_3 conf_3_1)) (not (= conf_4 conf_4_0)) (not (= t t_1)) (>= i_2 0)) (<= i 0)))



(define-fun pre-f ((c Int) (i Int) (j Int) (conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (t Int) (tmp Int) (c_0 Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (i_4 Int) (j_0 Int) (j_1 Int) (j_2 Int) (j_3 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_1_0 Int) (conf_1_1 Int) (conf_1_2 Int) (conf_1_3 Int) (conf_2_0 Int) (conf_3_0 Int) (conf_3_1 Int) (conf_3_2 Int) (conf_3_3 Int) (conf_4_0 Int) (t_0 Int) (t_1 Int) (t_2 Int) (t_3 Int)) Bool

    (and (= i i_1) (= conf_0 conf_0_0) (= conf_1 conf_1_0) (= conf_2 conf_2_0) (= conf_3 conf_3_0) (= conf_4 conf_4_0) (= conf_0_0 9) (= conf_1_0 0) (= conf_2_0 7) (= conf_3_0 4) (= conf_4_0 0) (= i_1 0)))

(define-fun trans-f ((c Int) (i Int) (j Int) (conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (t Int) (tmp Int) (c_0 Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (i_4 Int) (j_0 Int) (j_1 Int) (j_2 Int) (j_3 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_1_0 Int) (conf_1_1 Int) (conf_1_2 Int) (conf_1_3 Int) (conf_2_0 Int) (conf_3_0 Int) (conf_3_1 Int) (conf_3_2 Int) (conf_3_3 Int) (conf_4_0 Int) (t_0 Int) (t_1 Int) (t_2 Int) (t_3 Int) (c! Int) (i! Int) (j! Int) (conf_0! Int) (conf_1! Int) (conf_2! Int) (conf_3! Int) (conf_4! Int) (t! Int) (tmp! Int) (c_0! Int) (i_0! Int) (i_1! Int) (i_2! Int) (i_3! Int) (i_4! Int) (j_0! Int) (j_1! Int) (j_2! Int) (j_3! Int) (conf_0_0! Int) (conf_0_1! Int) (conf_0_2! Int) (conf_0_3! Int) (conf_1_0! Int) (conf_1_1! Int) (conf_1_2! Int) (conf_1_3! Int) (conf_2_0! Int) (conf_3_0! Int) (conf_3_1! Int) (conf_3_2! Int) (conf_3_3! Int) (conf_4_0! Int) (t_0! Int) (t_1! Int) (t_2! Int) (t_3! Int)) Bool

    (or (and (= i_2 i) (= j_1 j) (= conf_0_1 conf_0) (= conf_1_1 conf_1) (= conf_3_1 conf_3) (= t_1 t) (= i_2 i!) (= j_1 j!) (= conf_0_1 conf_0!) (= conf_1_1 conf_1!) (= conf_3_1 conf_3!) (= t_1 t!) (= c c!) (= i i!) (= j j!) (= conf_0 conf_0!) (= conf_1 conf_1!) (= conf_2 conf_2!) (= conf_3 conf_3!) (= conf_4 conf_4!) (= t t!) (= tmp tmp!)) (and (= i_2 i) (= j_1 j) (= conf_0_1 conf_0) (= conf_1_1 conf_1) (= conf_3_1 conf_3) (= t_1 t) (> c_0 48) (< c_0 57) (= j_2 (+ i_2 i_2)) (= conf_3_2 676) (= t_2 (- c_0 48)) (= conf_1_2 (- conf_0_1 conf_1_1)) (= i_3 (+ j_2 t_2)) (= conf_0_2 (+ 559 129)) (= i_4 i_3) (= j_3 j_2) (= conf_0_3 conf_0_2) (= conf_1_3 conf_1_2) (= conf_3_3 conf_3_2) (= t_3 t_2) (= i_4 i!) (= j_3 j!) (= conf_0_3 conf_0!) (= conf_1_3 conf_1!) (= conf_3_3 conf_3!) (= t_3 t!) (= c c_0) (= c! c_0) (= conf_2 conf_2_0) (= conf_2! conf_2_0) (= conf_4 conf_4_0) (= conf_4! conf_4_0) (= tmp tmp!)) (and (= i_2 i) (= j_1 j) (= conf_0_1 conf_0) (= conf_1_1 conf_1) (= conf_3_1 conf_3) (= t_1 t) (> c_0 48) (not (< c_0 57)) (= i_4 i_2) (= j_3 j_1) (= conf_0_3 conf_0_1) (= conf_1_3 conf_1_1) (= conf_3_3 conf_3_1) (= t_3 t_1) (= i_4 i!) (= j_3 j!) (= conf_0_3 conf_0!) (= conf_1_3 conf_1!) (= conf_3_3 conf_3!) (= t_3 t!) (= c c_0) (= c! c_0) (= conf_2 conf_2_0) (= conf_2! conf_2_0) (= conf_4 conf_4_0) (= conf_4! conf_4_0) (= tmp tmp!)) (and (= i_2 i) (= j_1 j) (= conf_0_1 conf_0) (= conf_1_1 conf_1) (= conf_3_1 conf_3) (= t_1 t) (not (> c_0 48)) (= i_4 i_2) (= j_3 j_1) (= conf_0_3 conf_0_1) (= conf_1_3 conf_1_1) (= conf_3_3 conf_3_1) (= t_3 t_1) (= i_4 i!) (= j_3 j!) (= conf_0_3 conf_0!) (= conf_1_3 conf_1!) (= conf_3_3 conf_3!) (= t_3 t!) (= c c_0) (= c! c_0) (= conf_2 conf_2_0) (= conf_2! conf_2_0) (= conf_4 conf_4_0) (= conf_4! conf_4_0) (= tmp tmp!))))

(define-fun post-f ((c Int) (i Int) (j Int) (conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (t Int) (tmp Int) (c_0 Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (i_4 Int) (j_0 Int) (j_1 Int) (j_2 Int) (j_3 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_1_0 Int) (conf_1_1 Int) (conf_1_2 Int) (conf_1_3 Int) (conf_2_0 Int) (conf_3_0 Int) (conf_3_1 Int) (conf_3_2 Int) (conf_3_3 Int) (conf_4_0 Int) (t_0 Int) (t_1 Int) (t_2 Int) (t_3 Int)) Bool

    (or (not (and (= c c_0) (= i i_2) (= j j_1) (= conf_0 conf_0_1) (= conf_1 conf_1_1) (= conf_2 conf_2_0) (= conf_3 conf_3_1) (= conf_4 conf_4_0) (= t t_1))) (not (not (>= i_2 0)))))





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

(assert
    (or
        (not (=> 
            (pre-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 ) 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 )
        ))


        (not (=>
            (and 
                (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 )
                (trans-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37  v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! v12! v13! v14! v15! v16! v17! v18! v19! v20! v21! v22! v23! v24! v25! v26! v27! v28! v29! v30! v31! v32! v33! v34! v35! v36! v37! )
            )
            (inv-f v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! v12! v13! v14! v15! v16! v17! v18! v19! v20! v21! v22! v23! v24! v25! v26! v27! v28! v29! v30! v31! v32! v33! v34! v35! v36! v37! )
        ))


        (not (=> 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 ) 
            (post-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 )
        ))
    )
)

(check-sat)
                