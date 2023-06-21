(set-logic LIA)

(define-fun inv-f ((c Int) (conf_0 Int) (y Int) (z Int) (tmp Int) (c_0 Int) (c_1 Int) (c_2 Int) (c_3 Int) (c_4 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (y_0 Int) (z_0 Int) (z_1 Int) (z_2 Int) (z_3 Int) (z_4 Int)) Bool (and (or (not (= c c_2)) (not (= conf_0 conf_0_1)) (not (= y y_0)) (not (= z z_2)) (>= z_2 0) (>= c_2 36)) (<= z 4608)))



(define-fun pre-f ((c Int) (conf_0 Int) (y Int) (z Int) (tmp Int) (c_0 Int) (c_1 Int) (c_2 Int) (c_3 Int) (c_4 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (y_0 Int) (z_0 Int) (z_1 Int) (z_2 Int) (z_3 Int) (z_4 Int)) Bool

    (and (= c c_1) (= conf_0 conf_0_0) (= y y_0) (= z z_1) (= conf_0_0 3) (= c_1 0) (>= y_0 0) (>= y_0 127) (= z_1 (* 36 y_0))))

(define-fun trans-f ((c Int) (conf_0 Int) (y Int) (z Int) (tmp Int) (c_0 Int) (c_1 Int) (c_2 Int) (c_3 Int) (c_4 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (y_0 Int) (z_0 Int) (z_1 Int) (z_2 Int) (z_3 Int) (z_4 Int) (c! Int) (conf_0! Int) (y! Int) (z! Int) (tmp! Int) (c_0! Int) (c_1! Int) (c_2! Int) (c_3! Int) (c_4! Int) (conf_0_0! Int) (conf_0_1! Int) (conf_0_2! Int) (conf_0_3! Int) (conf_0_4! Int) (y_0! Int) (z_0! Int) (z_1! Int) (z_2! Int) (z_3! Int) (z_4! Int)) Bool

    (or (and (= c_2 c) (= conf_0_1 conf_0) (= z_2 z) (= c_2 c!) (= conf_0_1 conf_0!) (= z_2 z!) (= c c!) (= conf_0 conf_0!) (= y y!) (= z z!) (= tmp tmp!)) (and (= c_2 c) (= conf_0_1 conf_0) (= z_2 z) (< c_2 36) (= z_3 (+ z_2 1)) (= conf_0_2 conf_0_1) (= c_3 (+ c_2 1)) (= conf_0_3 (+ conf_0_2 512)) (= c_4 c_3) (= conf_0_4 conf_0_3) (= z_4 z_3) (= c_4 c!) (= conf_0_4 conf_0!) (= z_4 z!) (= y y_0) (= y! y_0) (= tmp tmp!)) (and (= c_2 c) (= conf_0_1 conf_0) (= z_2 z) (not (< c_2 36)) (= c_4 c_2) (= conf_0_4 conf_0_1) (= z_4 z_2) (= c_4 c!) (= conf_0_4 conf_0!) (= z_4 z!) (= y y_0) (= y! y_0) (= tmp tmp!))))

(define-fun post-f ((c Int) (conf_0 Int) (y Int) (z Int) (tmp Int) (c_0 Int) (c_1 Int) (c_2 Int) (c_3 Int) (c_4 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (y_0 Int) (z_0 Int) (z_1 Int) (z_2 Int) (z_3 Int) (z_4 Int)) Bool

    (or (not (and (= c c_2) (= conf_0 conf_0_1) (= y y_0) (= z z_2))) (not (and (< z_2 0) (>= z_2 4608) (not (>= c_2 36))))))





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

(assert
    (or
        (not (=> 
            (pre-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 ) 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 )
        ))


        (not (=>
            (and 
                (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 )
                (trans-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20  v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! v12! v13! v14! v15! v16! v17! v18! v19! v20! )
            )
            (inv-f v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! v12! v13! v14! v15! v16! v17! v18! v19! v20! )
        ))


        (not (=> 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 ) 
            (post-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 )
        ))
    )
)

(check-sat)
                