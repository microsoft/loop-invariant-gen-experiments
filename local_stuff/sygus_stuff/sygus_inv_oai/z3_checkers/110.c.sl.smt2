(set-logic LIA)

(define-fun inv-f ((i Int) (n Int) (sn Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (n_0 Int) (sn_0 Int) (sn_1 Int) (sn_2 Int) (sn_3 Int)) Bool (and (or (not (= i i_2)) (not (= n n_0)) (not (= sn sn_2)) (<= i_2 n_0) (= sn_2 n_0) (= sn_2 0)) (<= sn n)))



(define-fun pre-f ((i Int) (n Int) (sn Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (n_0 Int) (sn_0 Int) (sn_1 Int) (sn_2 Int) (sn_3 Int)) Bool

    (and (= i i_1) (= sn sn_1) (= sn_1 0) (= i_1 1)))

(define-fun trans-f ((i Int) (n Int) (sn Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (n_0 Int) (sn_0 Int) (sn_1 Int) (sn_2 Int) (sn_3 Int) (i! Int) (n! Int) (sn! Int) (i_0! Int) (i_1! Int) (i_2! Int) (i_3! Int) (n_0! Int) (sn_0! Int) (sn_1! Int) (sn_2! Int) (sn_3! Int)) Bool

    (or (and (= i_2 i) (= sn_2 sn) (= i_2 i!) (= sn_2 sn!) (= n n_0) (= n! n_0) (= sn sn!)) (and (= i_2 i) (= sn_2 sn) (<= i_2 n_0) (= i_3 (+ i_2 1)) (= sn_3 (+ sn_2 1)) (= i_3 i!) (= sn_3 sn!) (= n n_0) (= n! n_0))))

(define-fun post-f ((i Int) (n Int) (sn Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (n_0 Int) (sn_0 Int) (sn_1 Int) (sn_2 Int) (sn_3 Int)) Bool

    (or (not (and (= i i_2) (= n n_0) (= sn sn_2))) (not (and (not (<= i_2 n_0)) (not (= sn_2 n_0)) (not (= sn_2 0))))))





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
                