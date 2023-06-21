(set-logic LIA)

(define-fun inv-f ((c Int) (n Int) (tmp Int) (c_0 Int) (c_1 Int) (c_2 Int) (c_3 Int) (c_4 Int) (c_5 Int) (n_0 Int)) Bool (and (or (not (= c c_2)) (not (= n n_0)) (>= c_2 0) (<= c_2 n_0)) (<= c n)))



(define-fun pre-f ((c Int) (n Int) (tmp Int) (c_0 Int) (c_1 Int) (c_2 Int) (c_3 Int) (c_4 Int) (c_5 Int) (n_0 Int)) Bool

    (and (= c c_1) (= n n_0) (= c_1 0) (> n_0 0)))

(define-fun trans-f ((c Int) (n Int) (tmp Int) (c_0 Int) (c_1 Int) (c_2 Int) (c_3 Int) (c_4 Int) (c_5 Int) (n_0 Int) (c! Int) (n! Int) (tmp! Int) (c_0! Int) (c_1! Int) (c_2! Int) (c_3! Int) (c_4! Int) (c_5! Int) (n_0! Int)) Bool

    (or (and (= c_2 c) (= c_2 c!) (= c c!) (= n n!) (= tmp tmp!)) (and (= c_2 c) (not (= c_2 n_0)) (= c_3 (+ c_2 1)) (= c_4 c_3) (= c_4 c!) (= n n_0) (= n! n_0) (= tmp tmp!)) (and (= c_2 c) (not (not (= c_2 n_0))) (= c_4 c_2) (= c_4 c!) (= n n_0) (= n! n_0) (= tmp tmp!)) (and (= c_2 c) (= c_2 n_0) (= c_5 1) (= c_4 c_5) (= c_4 c!) (= n n_0) (= n! n_0) (= tmp tmp!)) (and (= c_2 c) (not (= c_2 n_0)) (= c_4 c_2) (= c_4 c!) (= n n_0) (= n! n_0) (= tmp tmp!))))

(define-fun post-f ((c Int) (n Int) (tmp Int) (c_0 Int) (c_1 Int) (c_2 Int) (c_3 Int) (c_4 Int) (c_5 Int) (n_0 Int)) Bool

    (or (not (and (= c c_2) (= n n_0))) (not (and (< c_2 0) (> c_2 n_0) (not (= c_2 n_0))))))





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

(assert
    (or
        (not (=> 
            (pre-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 ) 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 )
        ))


        (not (=>
            (and 
                (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 )
                (trans-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9  v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! )
            )
            (inv-f v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! )
        ))


        (not (=> 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 ) 
            (post-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 )
        ))
    )
)

(check-sat)
                