(set-logic LIA)

(define-fun inv-f ((d1 Int) (d2 Int) (d3 Int) (conf_0 Int) (x1 Int) (x2 Int) (x3 Int) (d1_0 Int) (d1_1 Int) (d2_0 Int) (d2_1 Int) (d3_0 Int) (d3_1 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (conf_0_5 Int) (x1_0 Int) (x1_1 Int) (x1_2 Int) (x1_3 Int) (x1_4 Int) (x2_0 Int) (x2_1 Int) (x2_2 Int) (x2_3 Int) (x3_0 Int) (x3_1 Int) (x3_2 Int) (x3_3 Int)) Bool (and (or (not (= d1 d1_1)) (not (= d2 d2_1)) (not (= d3 d3_1)) (not (= conf_0 conf_0_1)) (not (= x1 x1_2)) (not (= x2 x2_1)) (not (= x3 x3_1)) (>= x1_2 1) (not (>= x3_1 0))) (<= x3 0)))



(define-fun pre-f ((d1 Int) (d2 Int) (d3 Int) (conf_0 Int) (x1 Int) (x2 Int) (x3 Int) (d1_0 Int) (d1_1 Int) (d2_0 Int) (d2_1 Int) (d3_0 Int) (d3_1 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (conf_0_5 Int) (x1_0 Int) (x1_1 Int) (x1_2 Int) (x1_3 Int) (x1_4 Int) (x2_0 Int) (x2_1 Int) (x2_2 Int) (x2_3 Int) (x3_0 Int) (x3_1 Int) (x3_2 Int) (x3_3 Int)) Bool

    (and (= d1 d1_1) (= d2 d2_1) (= d3 d3_1) (= conf_0 conf_0_0) (= x1 x1_1) (= conf_0_0 7) (= d1_1 1) (= d2_1 1) (= d3_1 1) (= x1_1 1)))

(define-fun trans-f ((d1 Int) (d2 Int) (d3 Int) (conf_0 Int) (x1 Int) (x2 Int) (x3 Int) (d1_0 Int) (d1_1 Int) (d2_0 Int) (d2_1 Int) (d3_0 Int) (d3_1 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (conf_0_5 Int) (x1_0 Int) (x1_1 Int) (x1_2 Int) (x1_3 Int) (x1_4 Int) (x2_0 Int) (x2_1 Int) (x2_2 Int) (x2_3 Int) (x3_0 Int) (x3_1 Int) (x3_2 Int) (x3_3 Int) (d1! Int) (d2! Int) (d3! Int) (conf_0! Int) (x1! Int) (x2! Int) (x3! Int) (d1_0! Int) (d1_1! Int) (d2_0! Int) (d2_1! Int) (d3_0! Int) (d3_1! Int) (conf_0_0! Int) (conf_0_1! Int) (conf_0_2! Int) (conf_0_3! Int) (conf_0_4! Int) (conf_0_5! Int) (x1_0! Int) (x1_1! Int) (x1_2! Int) (x1_3! Int) (x1_4! Int) (x2_0! Int) (x2_1! Int) (x2_2! Int) (x2_3! Int) (x3_0! Int) (x3_1! Int) (x3_2! Int) (x3_3! Int)) Bool

    (or (and (= conf_0_1 conf_0) (= x1_2 x1) (= x2_1 x2) (= x3_1 x3) (= conf_0_1 conf_0!) (= x1_2 x1!) (= x2_1 x2!) (= x3_1 x3!) (= d1 d1!) (= d2 d2!) (= d3 d3!) (= conf_0 conf_0!) (= x2 x2!) (= x3 x3!)) (and (= conf_0_1 conf_0) (= x1_2 x1) (= x2_1 x2) (= x3_1 x3) (> x1_2 0) (> x2_1 0) (> x3_1 0) (= x1_3 (- x1_2 d1_1)) (= conf_0_2 (- 24 conf_0_1)) (= x2_2 (- x2_1 d2_1)) (= conf_0_3 828) (= x3_2 (- x3_1 d3_1)) (= conf_0_4 (+ conf_0_3 435)) (= conf_0_5 conf_0_4) (= x1_4 x1_3) (= x2_3 x2_2) (= x3_3 x3_2) (= conf_0_5 conf_0!) (= x1_4 x1!) (= x2_3 x2!) (= x3_3 x3!) (= d1 d1_1) (= d1! d1_1) (= d2 d2_1) (= d2! d2_1) (= d3 d3_1) (= d3! d3_1)) (and (= conf_0_1 conf_0) (= x1_2 x1) (= x2_1 x2) (= x3_1 x3) (> x1_2 0) (> x2_1 0) (not (> x3_1 0)) (= conf_0_5 conf_0_1) (= x1_4 x1_2) (= x2_3 x2_1) (= x3_3 x3_1) (= conf_0_5 conf_0!) (= x1_4 x1!) (= x2_3 x2!) (= x3_3 x3!) (= d1 d1_1) (= d1! d1_1) (= d2 d2_1) (= d2! d2_1) (= d3 d3_1) (= d3! d3_1)) (and (= conf_0_1 conf_0) (= x1_2 x1) (= x2_1 x2) (= x3_1 x3) (> x1_2 0) (not (> x2_1 0)) (= conf_0_5 conf_0_1) (= x1_4 x1_2) (= x2_3 x2_1) (= x3_3 x3_1) (= conf_0_5 conf_0!) (= x1_4 x1!) (= x2_3 x2!) (= x3_3 x3!) (= d1 d1_1) (= d1! d1_1) (= d2 d2_1) (= d2! d2_1) (= d3 d3_1) (= d3! d3_1))))

(define-fun post-f ((d1 Int) (d2 Int) (d3 Int) (conf_0 Int) (x1 Int) (x2 Int) (x3 Int) (d1_0 Int) (d1_1 Int) (d2_0 Int) (d2_1 Int) (d3_0 Int) (d3_1 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (conf_0_5 Int) (x1_0 Int) (x1_1 Int) (x1_2 Int) (x1_3 Int) (x1_4 Int) (x2_0 Int) (x2_1 Int) (x2_2 Int) (x2_3 Int) (x3_0 Int) (x3_1 Int) (x3_2 Int) (x3_3 Int)) Bool

    (or (not (and (= d1 d1_1) (= d2 d2_1) (= d3 d3_1) (= conf_0 conf_0_1) (= x1 x1_2) (= x2 x2_1) (= x3 x3_1))) (not (and (not (> x1_2 0)) (not (>= x3_1 0))))))





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

(assert
    (or
        (not (=> 
            (pre-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 ) 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 )
        ))


        (not (=>
            (and 
                (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 )
                (trans-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31  v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! v12! v13! v14! v15! v16! v17! v18! v19! v20! v21! v22! v23! v24! v25! v26! v27! v28! v29! v30! v31! )
            )
            (inv-f v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! v12! v13! v14! v15! v16! v17! v18! v19! v20! v21! v22! v23! v24! v25! v26! v27! v28! v29! v30! v31! )
        ))


        (not (=> 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 ) 
            (post-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 )
        ))
    )
)

(check-sat)
                