(set-logic LIA)

(define-fun inv-f ((a Int) (c Int) (j Int) (conf_0 Int) (k Int) (m Int) (a_0 Int) (c_0 Int) (j_0 Int) (j_1 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (k_0 Int) (k_1 Int) (k_2 Int) (k_3 Int) (m_0 Int) (m_1 Int) (m_2 Int) (m_3 Int)) Bool (and (or (not (= a a_0)) (not (= c c_0)) (not (= j j_1)) (not (= conf_0 conf_0_1)) (not (= k k_2)) (not (= m m_1)) (>= k_2 c_0) (not (>= c_0 1)) (<= a_0 m_1)) (<= m a_0)))



(define-fun pre-f ((a Int) (c Int) (j Int) (conf_0 Int) (k Int) (m Int) (a_0 Int) (c_0 Int) (j_0 Int) (j_1 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (k_0 Int) (k_1 Int) (k_2 Int) (k_3 Int) (m_0 Int) (m_1 Int) (m_2 Int) (m_3 Int)) Bool

    (and (= j j_1) (= conf_0 conf_0_0) (= k k_1) (= conf_0_0 7) (= j_1 0) (= k_1 0)))

(define-fun trans-f ((a Int) (c Int) (j Int) (conf_0 Int) (k Int) (m Int) (a_0 Int) (c_0 Int) (j_0 Int) (j_1 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (k_0 Int) (k_1 Int) (k_2 Int) (k_3 Int) (m_0 Int) (m_1 Int) (m_2 Int) (m_3 Int) (a! Int) (c! Int) (j! Int) (conf_0! Int) (k! Int) (m! Int) (a_0! Int) (c_0! Int) (j_0! Int) (j_1! Int) (conf_0_0! Int) (conf_0_1! Int) (conf_0_2! Int) (conf_0_3! Int) (conf_0_4! Int) (k_0! Int) (k_1! Int) (k_2! Int) (k_3! Int) (m_0! Int) (m_1! Int) (m_2! Int) (m_3! Int)) Bool

    (or (and (= conf_0_1 conf_0) (= k_2 k) (= m_1 m) (= conf_0_1 conf_0!) (= k_2 k!) (= m_1 m!) (= c c_0) (= c! c_0) (= a a!) (= j j!) (= conf_0 conf_0!) (= m m!)) (and (= conf_0_1 conf_0) (= k_2 k) (= m_1 m) (< k_2 c_0) (< m_1 a_0) (= m_2 a_0) (= conf_0_2 conf_0_1) (= conf_0_3 conf_0_2) (= m_3 m_2) (= k_3 (+ k_2 1)) (= conf_0_4 (- conf_0_3 345)) (= conf_0_4 conf_0!) (= k_3 k!) (= m_3 m!) (= a a_0) (= a! a_0) (= c c_0) (= c! c_0) (= j j_1) (= j! j_1)) (and (= conf_0_1 conf_0) (= k_2 k) (= m_1 m) (< k_2 c_0) (not (< m_1 a_0)) (= conf_0_3 conf_0_1) (= m_3 m_1) (= k_3 (+ k_2 1)) (= conf_0_4 (- conf_0_3 345)) (= conf_0_4 conf_0!) (= k_3 k!) (= m_3 m!) (= a a_0) (= a! a_0) (= c c_0) (= c! c_0) (= j j_1) (= j! j_1))))

(define-fun post-f ((a Int) (c Int) (j Int) (conf_0 Int) (k Int) (m Int) (a_0 Int) (c_0 Int) (j_0 Int) (j_1 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (k_0 Int) (k_1 Int) (k_2 Int) (k_3 Int) (m_0 Int) (m_1 Int) (m_2 Int) (m_3 Int)) Bool

    (or (not (and (= a a_0) (= c c_0) (= j j_1) (= conf_0 conf_0_1) (= k k_2) (= m m_1))) (not (and (not (< k_2 c_0)) (> c_0 0) (not (<= a_0 m_1))))))





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
                