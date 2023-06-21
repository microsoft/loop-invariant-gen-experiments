(set-logic LIA)

(define-fun inv-f ((sn Int) (x Int) (tmp Int) (sn_0 Int) (sn_1 Int) (sn_2 Int) (sn_3 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int)) Bool (and (or (not (= sn sn_2)) (not (= x x_2)) (= sn_2 (- 1)) (= sn_2 x_2)) (>= sn 0)))



(define-fun pre-f ((sn Int) (x Int) (tmp Int) (sn_0 Int) (sn_1 Int) (sn_2 Int) (sn_3 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int)) Bool

    (and (= sn sn_1) (= x x_1) (= sn_1 0) (= x_1 0)))

(define-fun trans-f ((sn Int) (x Int) (tmp Int) (sn_0 Int) (sn_1 Int) (sn_2 Int) (sn_3 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (sn! Int) (x! Int) (tmp! Int) (sn_0! Int) (sn_1! Int) (sn_2! Int) (sn_3! Int) (x_0! Int) (x_1! Int) (x_2! Int) (x_3! Int)) Bool

    (or (and (= sn_2 sn) (= x_2 x) (= sn_2 sn!) (= x_2 x!) (= sn sn!) (= x x!) (= tmp tmp!)) (and (= sn_2 sn) (= x_2 x) (= x_3 (+ x_2 1)) (= sn_3 (+ sn_2 1)) (= sn_3 sn!) (= x_3 x!) (= tmp tmp!))))

(define-fun post-f ((sn Int) (x Int) (tmp Int) (sn_0 Int) (sn_1 Int) (sn_2 Int) (sn_3 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int)) Bool

    (or (not (and (= sn sn_2) (= x x_2))) (not (and (not (= sn_2 (- 1))) (not (= sn_2 x_2))))))





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

(assert
    (or
        (not (=> 
            (pre-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ) 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 )
        ))


        (not (=>
            (and 
                (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 )
                (trans-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10  v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! )
            )
            (inv-f v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! )
        ))


        (not (=> 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ) 
            (post-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 )
        ))
    )
)

(check-sat)
                