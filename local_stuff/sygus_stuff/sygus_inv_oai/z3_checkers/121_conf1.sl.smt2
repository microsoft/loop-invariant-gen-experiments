(set-logic LIA)

(define-fun inv-f ((i Int) (conf_0 Int) (sn Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (sn_0 Int) (sn_1 Int) (sn_2 Int) (sn_3 Int)) Bool (and (or (not (= i i_2)) (not (= conf_0 conf_0_1)) (not (= sn sn_2)) (<= i_2 8) (not (>= sn_2 1)) (not (<= sn_2 8))) (<= sn 8)))



(define-fun pre-f ((i Int) (conf_0 Int) (sn Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (sn_0 Int) (sn_1 Int) (sn_2 Int) (sn_3 Int)) Bool

    (and (= i i_1) (= conf_0 conf_0_0) (= sn sn_1) (= conf_0_0 4) (= sn_1 0) (= i_1 1)))

(define-fun trans-f ((i Int) (conf_0 Int) (sn Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (sn_0 Int) (sn_1 Int) (sn_2 Int) (sn_3 Int) (i! Int) (conf_0! Int) (sn! Int) (i_0! Int) (i_1! Int) (i_2! Int) (i_3! Int) (conf_0_0! Int) (conf_0_1! Int) (conf_0_2! Int) (conf_0_3! Int) (sn_0! Int) (sn_1! Int) (sn_2! Int) (sn_3! Int)) Bool

    (or (and (= i_2 i) (= conf_0_1 conf_0) (= sn_2 sn) (= i_2 i!) (= conf_0_1 conf_0!) (= sn_2 sn!) (= conf_0 conf_0!) (= sn sn!)) (and (= i_2 i) (= conf_0_1 conf_0) (= sn_2 sn) (<= i_2 8) (= i_3 (+ i_2 1)) (= conf_0_2 576) (= sn_3 (+ sn_2 1)) (= conf_0_3 (- conf_0_2 206)) (= i_3 i!) (= conf_0_3 conf_0!) (= sn_3 sn!))))

(define-fun post-f ((i Int) (conf_0 Int) (sn Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (sn_0 Int) (sn_1 Int) (sn_2 Int) (sn_3 Int)) Bool

    (or (not (and (= i i_2) (= conf_0 conf_0_1) (= sn sn_2))) (not (and (not (<= i_2 8)) (not (= sn_2 0)) (not (= sn_2 8))))))





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

(assert
    (or
        (not (=> 
            (pre-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 ) 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 )
        ))


        (not (=>
            (and 
                (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 )
                (trans-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14  v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! v12! v13! v14! )
            )
            (inv-f v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! v12! v13! v14! )
        ))


        (not (=> 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 ) 
            (post-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 )
        ))
    )
)

(check-sat)
                