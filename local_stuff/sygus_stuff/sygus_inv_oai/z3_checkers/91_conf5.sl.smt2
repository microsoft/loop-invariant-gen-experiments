(set-logic LIA)

(define-fun inv-f ((conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (x Int) (y Int) (conf_0_0 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_3_0 Int) (conf_3_1 Int) (conf_3_2 Int) (conf_4_0 Int) (x_0 Int) (x_1 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int)) Bool (and (or (not (= conf_0 conf_0_0)) (not (= conf_1 conf_1_0)) (not (= conf_2 conf_2_0)) (not (= conf_3 conf_3_1)) (not (= conf_4 conf_4_0)) (not (= x x_1)) (not (= y y_2)) (>= y_2 1) (>= y_2 0)) (<= y 0)))



(define-fun pre-f ((conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (x Int) (y Int) (conf_0_0 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_3_0 Int) (conf_3_1 Int) (conf_3_2 Int) (conf_4_0 Int) (x_0 Int) (x_1 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int)) Bool

    (and (= conf_0 conf_0_0) (= conf_1 conf_1_0) (= conf_2 conf_2_0) (= conf_3 conf_3_0) (= conf_4 conf_4_0) (= x x_1) (= y y_1) (= conf_0_0 5) (= conf_1_0 3) (= conf_2_0 4) (= conf_3_0 3) (= conf_4_0 8) (= x_1 0) (= y_1 0)))

(define-fun trans-f ((conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (x Int) (y Int) (conf_0_0 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_3_0 Int) (conf_3_1 Int) (conf_3_2 Int) (conf_4_0 Int) (x_0 Int) (x_1 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int) (conf_0! Int) (conf_1! Int) (conf_2! Int) (conf_3! Int) (conf_4! Int) (x! Int) (y! Int) (conf_0_0! Int) (conf_1_0! Int) (conf_2_0! Int) (conf_3_0! Int) (conf_3_1! Int) (conf_3_2! Int) (conf_4_0! Int) (x_0! Int) (x_1! Int) (y_0! Int) (y_1! Int) (y_2! Int) (y_3! Int)) Bool

    (or (and (= conf_3_1 conf_3) (= y_2 y) (= conf_3_1 conf_3!) (= y_2 y!) (= conf_0 conf_0!) (= conf_1 conf_1!) (= conf_2 conf_2!) (= conf_3 conf_3!) (= conf_4 conf_4!) (= x x!)) (and (= conf_3_1 conf_3) (= y_2 y) (>= y_2 0) (= y_3 (+ y_2 x_1)) (= conf_3_2 (+ conf_2_0 917)) (= conf_3_2 conf_3!) (= y_3 y!) (= conf_0 conf_0_0) (= conf_0! conf_0_0) (= conf_1 conf_1_0) (= conf_1! conf_1_0) (= conf_2 conf_2_0) (= conf_2! conf_2_0) (= conf_4 conf_4_0) (= conf_4! conf_4_0) (= x x_1) (= x! x_1))))

(define-fun post-f ((conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (x Int) (y Int) (conf_0_0 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_3_0 Int) (conf_3_1 Int) (conf_3_2 Int) (conf_4_0 Int) (x_0 Int) (x_1 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int)) Bool

    (or (not (and (= conf_0 conf_0_0) (= conf_1 conf_1_0) (= conf_2 conf_2_0) (= conf_3 conf_3_1) (= conf_4 conf_4_0) (= x x_1) (= y y_2))) (not (and (not (>= y_2 0)) (not (>= y_2 0))))))





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

(assert
    (or
        (not (=> 
            (pre-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 ) 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 )
        ))


        (not (=>
            (and 
                (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 )
                (trans-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19  v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! v12! v13! v14! v15! v16! v17! v18! v19! )
            )
            (inv-f v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! v12! v13! v14! v15! v16! v17! v18! v19! )
        ))


        (not (=> 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 ) 
            (post-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 )
        ))
    )
)

(check-sat)
                