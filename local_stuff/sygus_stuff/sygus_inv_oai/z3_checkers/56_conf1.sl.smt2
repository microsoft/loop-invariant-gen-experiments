(set-logic LIA)

(define-fun inv-f ((c Int) (conf_0 Int) (n Int) (tmp Int) (c_0 Int) (c_1 Int) (c_2 Int) (c_3 Int) (c_4 Int) (c_5 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (n_0 Int)) Bool (and (or (not (= c c_2)) (not (= conf_0 conf_0_1)) (not (= n n_0)) (<= n_0 (- 1)) (not (= c_2 n_0))) (<= c n_0)))



(define-fun pre-f ((c Int) (conf_0 Int) (n Int) (tmp Int) (c_0 Int) (c_1 Int) (c_2 Int) (c_3 Int) (c_4 Int) (c_5 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (n_0 Int)) Bool

    (and (= c c_1) (= conf_0 conf_0_0) (= n n_0) (= conf_0_0 3) (= c_1 0) (> n_0 0)))

(define-fun trans-f ((c Int) (conf_0 Int) (n Int) (tmp Int) (c_0 Int) (c_1 Int) (c_2 Int) (c_3 Int) (c_4 Int) (c_5 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (n_0 Int) (c! Int) (conf_0! Int) (n! Int) (tmp! Int) (c_0! Int) (c_1! Int) (c_2! Int) (c_3! Int) (c_4! Int) (c_5! Int) (conf_0_0! Int) (conf_0_1! Int) (conf_0_2! Int) (conf_0_3! Int) (conf_0_4! Int) (n_0! Int)) Bool

    (or (and (= c_2 c) (= conf_0_1 conf_0) (= c_2 c!) (= conf_0_1 conf_0!) (= c c!) (= conf_0 conf_0!) (= n n!) (= tmp tmp!)) (and (= c_2 c) (= conf_0_1 conf_0) (> c_2 n_0) (= c_3 (+ c_2 1)) (= conf_0_2 (+ conf_0_1 585)) (= c_4 c_3) (= conf_0_3 conf_0_2) (= c_4 c!) (= conf_0_3 conf_0!) (= n n_0) (= n! n_0) (= tmp tmp!)) (and (= c_2 c) (= conf_0_1 conf_0) (not (> c_2 n_0)) (= c_4 c_2) (= conf_0_3 conf_0_1) (= c_4 c!) (= conf_0_3 conf_0!) (= n n_0) (= n! n_0) (= tmp tmp!)) (and (= c_2 c) (= conf_0_1 conf_0) (= c_2 n_0) (= c_5 1) (= conf_0_4 (- conf_0_1 conf_0_1)) (= c_4 c_5) (= conf_0_3 conf_0_4) (= c_4 c!) (= conf_0_3 conf_0!) (= n n_0) (= n! n_0) (= tmp tmp!)) (and (= c_2 c) (= conf_0_1 conf_0) (not (= c_2 n_0)) (= c_4 c_2) (= conf_0_3 conf_0_1) (= c_4 c!) (= conf_0_3 conf_0!) (= n n_0) (= n! n_0) (= tmp tmp!))))

(define-fun post-f ((c Int) (conf_0 Int) (n Int) (tmp Int) (c_0 Int) (c_1 Int) (c_2 Int) (c_3 Int) (c_4 Int) (c_5 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (n_0 Int)) Bool

    (or (not (and (= c c_2) (= conf_0 conf_0_1) (= n n_0))) (not (and (= c_2 n_0) (not (<= n_0 (- 1)))))))





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

(assert
    (or
        (not (=> 
            (pre-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 ) 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 )
        ))


        (not (=>
            (and 
                (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 )
                (trans-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15  v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! v12! v13! v14! v15! )
            )
            (inv-f v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! v12! v13! v14! v15! )
        ))


        (not (=> 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 ) 
            (post-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 )
        ))
    )
)

(check-sat)
                