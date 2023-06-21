(set-logic LIA)

(define-fun inv-f ((i Int) (j Int) (conf_0 Int) (k Int) (n Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (j_0 Int) (j_1 Int) (j_2 Int) (j_3 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (k_0 Int) (n_0 Int)) Bool (and (or (not (= i i_2)) (not (= j j_2)) (not (= conf_0 conf_0_1)) (not (= k k_0)) (not (= n n_0)) (<= i_2 n_0) (>= (+ i_2 (+ j_2 k_0)) (* 2 n_0))) (<= n_0 0)) (>= j 0) (>= conf_0 0)))



(define-fun pre-f ((i Int) (j Int) (conf_0 Int) (k Int) (n Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (j_0 Int) (j_1 Int) (j_2 Int) (j_3 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (k_0 Int) (n_0 Int)) Bool

    (and (= i i_1) (= j j_1) (= conf_0 conf_0_0) (= k k_0) (= n n_0) (= conf_0_0 9) (>= k_0 0) (>= n_0 0) (= i_1 0) (= j_1 0)))

(define-fun trans-f ((i Int) (j Int) (conf_0 Int) (k Int) (n Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (j_0 Int) (j_1 Int) (j_2 Int) (j_3 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (k_0 Int) (n_0 Int) (i! Int) (j! Int) (conf_0! Int) (k! Int) (n! Int) (i_0! Int) (i_1! Int) (i_2! Int) (i_3! Int) (j_0! Int) (j_1! Int) (j_2! Int) (j_3! Int) (conf_0_0! Int) (conf_0_1! Int) (conf_0_2! Int) (conf_0_3! Int) (k_0! Int) (n_0! Int)) Bool

    (or (and (= i_2 i) (= j_2 j) (= conf_0_1 conf_0) (= i_2 i!) (= j_2 j!) (= conf_0_1 conf_0!) (= n n_0) (= n! n_0) (= j j!) (= conf_0 conf_0!) (= k k!)) (and (= i_2 i) (= j_2 j) (= conf_0_1 conf_0) (<= i_2 n_0) (= i_3 (+ i_2 1)) (= conf_0_2 153) (= j_3 (+ j_2 i_3)) (= conf_0_3 (+ 205 conf_0_2)) (= i_3 i!) (= j_3 j!) (= conf_0_3 conf_0!) (= k k_0) (= k! k_0) (= n n_0) (= n! n_0))))

(define-fun post-f ((i Int) (j Int) (conf_0 Int) (k Int) (n Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (j_0 Int) (j_1 Int) (j_2 Int) (j_3 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (k_0 Int) (n_0 Int)) Bool

    (or (not (and (= i i_2) (= j j_2) (= conf_0 conf_0_1) (= k k_0) (= n n_0))) (not (and (not (<= i_2 n_0)) (not (> (+ i_2 (+ j_2 k_0)) (* 2 n_0)))))))





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

(assert
    (or
        (not (=> 
            (pre-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 ) 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 )
        ))


        (not (=>
            (and 
                (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 )
                (trans-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18  v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! v12! v13! v14! v15! v16! v17! v18! )
            )
            (inv-f v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! v12! v13! v14! v15! v16! v17! v18! )
        ))


        (not (=> 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 ) 
            (post-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 )
        ))
    )
)

(check-sat)
                