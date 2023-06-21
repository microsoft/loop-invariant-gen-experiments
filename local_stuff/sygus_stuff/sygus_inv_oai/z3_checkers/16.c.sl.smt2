(set-logic LIA)

(define-fun inv-f ((m Int) (n Int) (x Int) (tmp Int) (m_0 Int) (m_1 Int) (m_2 Int) (m_3 Int) (n_0 Int) (x_0 Int) (x_1 Int) (x_2 Int)) Bool (and (or (not (= m m_1)) (not (= n n_0)) (not (= x x_1)) (>= (+ n_0 (* (- 1) x_1)) 1) (not (>= n_0 1)) (not (>= (+ m_1 (* (- 1) n_0)) 0))) (not (>= (+ m (* (- 1) x)) 1))))



(define-fun pre-f ((m Int) (n Int) (x Int) (tmp Int) (m_0 Int) (m_1 Int) (m_2 Int) (m_3 Int) (n_0 Int) (x_0 Int) (x_1 Int) (x_2 Int)) Bool

    (and (= m m_0) (= x x_0) (= x_0 0) (= m_0 0)))

(define-fun trans-f ((m Int) (n Int) (x Int) (tmp Int) (m_0 Int) (m_1 Int) (m_2 Int) (m_3 Int) (n_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (m! Int) (n! Int) (x! Int) (tmp! Int) (m_0! Int) (m_1! Int) (m_2! Int) (m_3! Int) (n_0! Int) (x_0! Int) (x_1! Int) (x_2! Int)) Bool

    (or (and (= m_1 m) (= x_1 x) (= m_1 m!) (= x_1 x!) (= n n_0) (= n! n_0) (= m m!) (= tmp tmp!)) (and (= m_1 m) (= x_1 x) (< x_1 n_0) (= m_2 x_1) (= m_3 m_2) (= x_2 (+ x_1 1)) (= m_3 m!) (= x_2 x!) (= n n_0) (= n! n_0) (= tmp tmp!)) (and (= m_1 m) (= x_1 x) (< x_1 n_0) (= m_3 m_1) (= x_2 (+ x_1 1)) (= m_3 m!) (= x_2 x!) (= n n_0) (= n! n_0) (= tmp tmp!))))

(define-fun post-f ((m Int) (n Int) (x Int) (tmp Int) (m_0 Int) (m_1 Int) (m_2 Int) (m_3 Int) (n_0 Int) (x_0 Int) (x_1 Int) (x_2 Int)) Bool

    (or (not (and (= m m_1) (= n n_0) (= x x_1))) (not (and (not (< x_1 n_0)) (> n_0 0) (not (>= m_1 0))))))





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

(assert
    (or
        (not (=> 
            (pre-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 ) 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 )
        ))


        (not (=>
            (and 
                (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 )
                (trans-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11  v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! )
            )
            (inv-f v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! )
        ))


        (not (=> 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 ) 
            (post-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 )
        ))
    )
)

(check-sat)
                