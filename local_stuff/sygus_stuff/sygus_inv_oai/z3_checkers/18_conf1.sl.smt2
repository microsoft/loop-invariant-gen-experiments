(set-logic LIA)

(define-fun inv-f ((conf_0 Int) (m Int) (n Int) (x Int) (tmp Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (m_0 Int) (m_1 Int) (m_2 Int) (m_3 Int) (m_4 Int) (n_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int)) Bool (and (or (not (= conf_0 conf_0_1)) (not (= m m_2)) (not (= n n_0)) (not (= x x_2)) (>= x_2 n_0) (not (>= n_0 2)) (>= m_2 1)) (<= m 1)))



(define-fun pre-f ((conf_0 Int) (m Int) (n Int) (x Int) (tmp Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (m_0 Int) (m_1 Int) (m_2 Int) (m_3 Int) (m_4 Int) (n_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int)) Bool

    (and (= conf_0 conf_0_0) (= m m_1) (= x x_1) (= conf_0_0 8) (= x_1 1) (= m_1 1)))

(define-fun trans-f ((conf_0 Int) (m Int) (n Int) (x Int) (tmp Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (m_0 Int) (m_1 Int) (m_2 Int) (m_3 Int) (m_4 Int) (n_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (conf_0! Int) (m! Int) (n! Int) (x! Int) (tmp! Int) (conf_0_0! Int) (conf_0_1! Int) (conf_0_2! Int) (conf_0_3! Int) (conf_0_4! Int) (m_0! Int) (m_1! Int) (m_2! Int) (m_3! Int) (m_4! Int) (n_0! Int) (x_0! Int) (x_1! Int) (x_2! Int) (x_3! Int)) Bool

    (or (and (= conf_0_1 conf_0) (= m_2 m) (= x_2 x) (= conf_0_1 conf_0!) (= m_2 m!) (= x_2 x!) (= n n_0) (= n! n_0) (= conf_0 conf_0!) (= m m!) (= tmp tmp!)) (and (= conf_0_1 conf_0) (= m_2 m) (= x_2 x) (< x_2 n_0) (= m_3 x_2) (= conf_0_2 (- 807 conf_0_1)) (= conf_0_3 conf_0_2) (= m_4 m_3) (= x_3 (+ x_2 1)) (= conf_0_4 (+ 715 695)) (= conf_0_4 conf_0!) (= m_4 m!) (= x_3 x!) (= n n_0) (= n! n_0) (= tmp tmp!)) (and (= conf_0_1 conf_0) (= m_2 m) (= x_2 x) (< x_2 n_0) (= conf_0_3 conf_0_1) (= m_4 m_2) (= x_3 (+ x_2 1)) (= conf_0_4 (+ 715 695)) (= conf_0_4 conf_0!) (= m_4 m!) (= x_3 x!) (= n n_0) (= n! n_0) (= tmp tmp!))))

(define-fun post-f ((conf_0 Int) (m Int) (n Int) (x Int) (tmp Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (m_0 Int) (m_1 Int) (m_2 Int) (m_3 Int) (m_4 Int) (n_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int)) Bool

    (or (not (and (= conf_0 conf_0_1) (= m m_2) (= n n_0) (= x x_2))) (not (and (not (< x_2 n_0)) (> n_0 1) (not (>= m_2 1))))))





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
                