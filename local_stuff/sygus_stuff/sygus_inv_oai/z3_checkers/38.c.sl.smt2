(set-logic LIA)

(define-fun inv-f ((c Int) (n Int) (tmp Int) (c_0 Int) (c_1 Int) (c_2 Int) (c_3 Int) (c_4 Int) (n_0 Int)) Bool (and (or (not (= c c_1)) (not (= n n_0)) (>= c_1 0) (not (= c_1 n_0))) (<= c n_0)))



(define-fun pre-f ((c Int) (n Int) (tmp Int) (c_0 Int) (c_1 Int) (c_2 Int) (c_3 Int) (c_4 Int) (n_0 Int)) Bool

    (and (= c c_0) (= n n_0) (= c_0 0) (> n_0 0)))

(define-fun trans-f ((c Int) (n Int) (tmp Int) (c_0 Int) (c_1 Int) (c_2 Int) (c_3 Int) (c_4 Int) (n_0 Int) (c! Int) (n! Int) (tmp! Int) (c_0! Int) (c_1! Int) (c_2! Int) (c_3! Int) (c_4! Int) (n_0! Int)) Bool

    (or (and (= c_1 c) (= c_1 c!) (= c c!) (= n n!) (= tmp tmp!)) (and (= c_1 c) (= c_1 n_0) (= c_2 1) (= c_3 c_2) (= c_3 c!) (= n n_0) (= n! n_0) (= tmp tmp!)) (and (= c_1 c) (not (= c_1 n_0)) (= c_4 (+ c_1 1)) (= c_3 c_4) (= c_3 c!) (= n n_0) (= n! n_0) (= tmp tmp!))))

(define-fun post-f ((c Int) (n Int) (tmp Int) (c_0 Int) (c_1 Int) (c_2 Int) (c_3 Int) (c_4 Int) (n_0 Int)) Bool

    (or (not (and (= c c_1) (= n n_0))) (not (and (= c_1 n_0) (not (>= c_1 0))))))





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

(assert
    (or
        (not (=> 
            (pre-f v0 v1 v2 v3 v4 v5 v6 v7 v8 ) 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 )
        ))


        (not (=>
            (and 
                (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 )
                (trans-f v0 v1 v2 v3 v4 v5 v6 v7 v8  v0! v1! v2! v3! v4! v5! v6! v7! v8! )
            )
            (inv-f v0! v1! v2! v3! v4! v5! v6! v7! v8! )
        ))


        (not (=> 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 ) 
            (post-f v0 v1 v2 v3 v4 v5 v6 v7 v8 )
        ))
    )
)

(check-sat)
                