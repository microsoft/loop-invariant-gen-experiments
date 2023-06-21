(set-logic LIA)

(define-fun inv-f ((conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (x Int) (y Int) (tmp Int) (conf_0_0 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_2_1 Int) (conf_2_2 Int) (conf_3_0 Int) (conf_3_1 Int) (conf_3_2 Int) (conf_4_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (y_0 Int) (y_1 Int) (y_2 Int)) Bool (and (or (not (= conf_0 conf_0_0)) (not (= conf_1 conf_1_0)) (not (= conf_2 conf_2_1)) (not (= conf_3 conf_3_1)) (not (= conf_4 conf_4_0)) (not (= x x_1)) (not (= y y_1)) (not (= x_1 20)) (not (= y_1 0))) (<= x 20) (<= y 0)))



(define-fun pre-f ((conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (x Int) (y Int) (tmp Int) (conf_0_0 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_2_1 Int) (conf_2_2 Int) (conf_3_0 Int) (conf_3_1 Int) (conf_3_2 Int) (conf_4_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (y_0 Int) (y_1 Int) (y_2 Int)) Bool

    (and (= conf_0 conf_0_0) (= conf_1 conf_1_0) (= conf_2 conf_2_0) (= conf_3 conf_3_0) (= conf_4 conf_4_0) (= x x_0) (= y y_0) (= conf_0_0 3) (= conf_1_0 3) (= conf_2_0 3) (= conf_3_0 9) (= conf_4_0 3) (>= x_0 0) (<= x_0 10) (<= y_0 10) (>= y_0 0)))

(define-fun trans-f ((conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (x Int) (y Int) (tmp Int) (conf_0_0 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_2_1 Int) (conf_2_2 Int) (conf_3_0 Int) (conf_3_1 Int) (conf_3_2 Int) (conf_4_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (y_0 Int) (y_1 Int) (y_2 Int) (conf_0! Int) (conf_1! Int) (conf_2! Int) (conf_3! Int) (conf_4! Int) (x! Int) (y! Int) (tmp! Int) (conf_0_0! Int) (conf_1_0! Int) (conf_2_0! Int) (conf_2_1! Int) (conf_2_2! Int) (conf_3_0! Int) (conf_3_1! Int) (conf_3_2! Int) (conf_4_0! Int) (x_0! Int) (x_1! Int) (x_2! Int) (y_0! Int) (y_1! Int) (y_2! Int)) Bool

    (or (and (= conf_2_1 conf_2) (= conf_3_1 conf_3) (= x_1 x) (= y_1 y) (= conf_2_1 conf_2!) (= conf_3_1 conf_3!) (= x_1 x!) (= y_1 y!) (= conf_0 conf_0!) (= conf_1 conf_1!) (= conf_2 conf_2!) (= conf_3 conf_3!) (= conf_4 conf_4!) (= x x!) (= y y!) (= tmp tmp!)) (and (= conf_2_1 conf_2) (= conf_3_1 conf_3) (= x_1 x) (= y_1 y) (= x_2 (+ x_1 10)) (= conf_3_2 588) (= y_2 (+ y_1 10)) (= conf_2_2 353) (= conf_2_2 conf_2!) (= conf_3_2 conf_3!) (= x_2 x!) (= y_2 y!) (= conf_0 conf_0_0) (= conf_0! conf_0_0) (= conf_1 conf_1_0) (= conf_1! conf_1_0) (= conf_4 conf_4_0) (= conf_4! conf_4_0) (= tmp tmp!))))

(define-fun post-f ((conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (x Int) (y Int) (tmp Int) (conf_0_0 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_2_1 Int) (conf_2_2 Int) (conf_3_0 Int) (conf_3_1 Int) (conf_3_2 Int) (conf_4_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (y_0 Int) (y_1 Int) (y_2 Int)) Bool

    (or (not (and (= conf_0 conf_0_0) (= conf_1 conf_1_0) (= conf_2 conf_2_1) (= conf_3 conf_3_1) (= conf_4 conf_4_0) (= x x_1) (= y y_1))) (not (and (= x_1 20) (not (not (= y_1 0)))))))





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

(assert
    (or
        (not (=> 
            (pre-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 ) 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 )
        ))


        (not (=>
            (and 
                (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 )
                (trans-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22  v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! v12! v13! v14! v15! v16! v17! v18! v19! v20! v21! v22! )
            )
            (inv-f v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! v12! v13! v14! v15! v16! v17! v18! v19! v20! v21! v22! )
        ))


        (not (=> 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 ) 
            (post-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 )
        ))
    )
)

(check-sat)
                