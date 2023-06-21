(set-logic LIA)

(define-fun inv-f ((a Int) (j Int) (k Int) (m Int) (a_0 Int) (j_0 Int) (k_0 Int) (k_1 Int) (k_2 Int) (k_3 Int) (m_0 Int) (m_1 Int) (m_2 Int) (m_3 Int)) Bool (and (or (not (= a a_0)) (not (= j j_0)) (not (= k k_2)) (not (= m m_1)) (>= k_2 1) (>= a_0 m_1)) (<= k 1)))



(define-fun pre-f ((a Int) (j Int) (k Int) (m Int) (a_0 Int) (j_0 Int) (k_0 Int) (k_1 Int) (k_2 Int) (k_3 Int) (m_0 Int) (m_1 Int) (m_2 Int) (m_3 Int)) Bool

    (and (= a a_0) (= j j_0) (= k k_1) (= m m_0) (<= a_0 m_0) (< j_0 1) (= k_1 0)))

(define-fun trans-f ((a Int) (j Int) (k Int) (m Int) (a_0 Int) (j_0 Int) (k_0 Int) (k_1 Int) (k_2 Int) (k_3 Int) (m_0 Int) (m_1 Int) (m_2 Int) (m_3 Int) (a! Int) (j! Int) (k! Int) (m! Int) (a_0! Int) (j_0! Int) (k_0! Int) (k_1! Int) (k_2! Int) (k_3! Int) (m_0! Int) (m_1! Int) (m_2! Int) (m_3! Int)) Bool

    (or (and (= k_2 k) (= m_1 m) (= k_2 k!) (= m_1 m!) (= a a!) (= j j!) (= m m!)) (and (= k_2 k) (= m_1 m) (< k_2 1) (< m_1 a_0) (= m_2 a_0) (= m_3 m_2) (= k_3 (+ k_2 1)) (= k_3 k!) (= m_3 m!) (= a a_0) (= a! a_0) (= j j_0) (= j! j_0)) (and (= k_2 k) (= m_1 m) (< k_2 1) (not (< m_1 a_0)) (= m_3 m_1) (= k_3 (+ k_2 1)) (= k_3 k!) (= m_3 m!) (= a a_0) (= a! a_0) (= j j_0) (= j! j_0))))

(define-fun post-f ((a Int) (j Int) (k Int) (m Int) (a_0 Int) (j_0 Int) (k_0 Int) (k_1 Int) (k_2 Int) (k_3 Int) (m_0 Int) (m_1 Int) (m_2 Int) (m_3 Int)) Bool

    (or (not (and (= a a_0) (= j j_0) (= k k_2) (= m m_1))) (not (and (not (< k_2 1)) (not (>= a_0 m_1))))))





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

(assert
    (or
        (not (=> 
            (pre-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 ) 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 )
        ))


        (not (=>
            (and 
                (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 )
                (trans-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13  v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! v12! v13! )
            )
            (inv-f v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! v12! v13! )
        ))


        (not (=> 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 ) 
            (post-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 )
        ))
    )
)

(check-sat)
                