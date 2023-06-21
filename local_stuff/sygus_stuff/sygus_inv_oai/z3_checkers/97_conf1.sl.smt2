(set-logic LIA)

(define-fun inv-f ((i Int) (j Int) (conf_0 Int) (x Int) (y Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (j_0 Int) (j_1 Int) (j_2 Int) (j_3 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (x_0 Int) (y_0 Int) (y_1 Int)) Bool (and (or (not (= i i_2)) (not (= j j_2)) (not (= conf_0 conf_0_1)) (not (= x x_0)) (not (= y y_1)) (<= i_2 x_0) (not (= y_1 1)) (not (= i_2 j_2))) (<= j 2)))



(define-fun pre-f ((i Int) (j Int) (conf_0 Int) (x Int) (y Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (j_0 Int) (j_1 Int) (j_2 Int) (j_3 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (x_0 Int) (y_0 Int) (y_1 Int)) Bool

    (and (= i i_1) (= j j_1) (= conf_0 conf_0_0) (= y y_1) (= conf_0_0 8) (= j_1 0) (= i_1 0) (= y_1 2)))

(define-fun trans-f ((i Int) (j Int) (conf_0 Int) (x Int) (y Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (j_0 Int) (j_1 Int) (j_2 Int) (j_3 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (x_0 Int) (y_0 Int) (y_1 Int) (i! Int) (j! Int) (conf_0! Int) (x! Int) (y! Int) (i_0! Int) (i_1! Int) (i_2! Int) (i_3! Int) (j_0! Int) (j_1! Int) (j_2! Int) (j_3! Int) (conf_0_0! Int) (conf_0_1! Int) (conf_0_2! Int) (conf_0_3! Int) (x_0! Int) (y_0! Int) (y_1! Int)) Bool

    (or (and (= i_2 i) (= j_2 j) (= conf_0_1 conf_0) (= i_2 i!) (= j_2 j!) (= conf_0_1 conf_0!) (= x x_0) (= x! x_0) (= j j!) (= conf_0 conf_0!) (= y y!)) (and (= i_2 i) (= j_2 j) (= conf_0_1 conf_0) (<= i_2 x_0) (= i_3 (+ i_2 1)) (= conf_0_2 (+ conf_0_1 conf_0_1)) (= j_3 (+ j_2 y_1)) (= conf_0_3 (- 293 conf_0_2)) (= i_3 i!) (= j_3 j!) (= conf_0_3 conf_0!) (= x x_0) (= x! x_0) (= y y_1) (= y! y_1))))

(define-fun post-f ((i Int) (j Int) (conf_0 Int) (x Int) (y Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (j_0 Int) (j_1 Int) (j_2 Int) (j_3 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (x_0 Int) (y_0 Int) (y_1 Int)) Bool

    (or (not (and (= i i_2) (= j j_2) (= conf_0 conf_0_1) (= x x_0) (= y y_1))) (not (and (not (<= i_2 x_0)) (= y_1 1) (not (= i_2 j_2))))))





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
                