(set-logic LIA)

(define-fun inv-f ((i Int) (conf_0 Int) (x Int) (y Int) (tmp Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (i_4 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (x_0 Int) (y_0 Int)) Bool (and (or (not (= i i_2)) (not (= conf_0 conf_0_1)) (not (= x x_0)) (not (= y y_0)) (>= i_2 x_0) (<= i_2 0) (>= i_2 y_0)) (>= i 0) (<= i y)))



(define-fun pre-f ((i Int) (conf_0 Int) (x Int) (y Int) (tmp Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (i_4 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (x_0 Int) (y_0 Int)) Bool

    (and (= i i_1) (= conf_0 conf_0_0) (= x x_0) (= y y_0) (= conf_0_0 2) (= i_1 0) (>= x_0 0) (>= y_0 0) (>= x_0 y_0)))

(define-fun trans-f ((i Int) (conf_0 Int) (x Int) (y Int) (tmp Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (i_4 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (x_0 Int) (y_0 Int) (i! Int) (conf_0! Int) (x! Int) (y! Int) (tmp! Int) (i_0! Int) (i_1! Int) (i_2! Int) (i_3! Int) (i_4! Int) (conf_0_0! Int) (conf_0_1! Int) (conf_0_2! Int) (conf_0_3! Int) (x_0! Int) (y_0! Int)) Bool

    (or (and (= i_2 i) (= conf_0_1 conf_0) (= i_2 i!) (= conf_0_1 conf_0!) (= i i!) (= conf_0 conf_0!) (= x x!) (= y y!) (= tmp tmp!)) (and (= i_2 i) (= conf_0_1 conf_0) (< i_2 y_0) (= i_3 (+ i_2 1)) (= conf_0_2 (- 161 conf_0_1)) (= i_4 i_3) (= conf_0_3 conf_0_2) (= i_4 i!) (= conf_0_3 conf_0!) (= x x_0) (= x! x_0) (= y y_0) (= y! y_0) (= tmp tmp!)) (and (= i_2 i) (= conf_0_1 conf_0) (not (< i_2 y_0)) (= i_4 i_2) (= conf_0_3 conf_0_1) (= i_4 i!) (= conf_0_3 conf_0!) (= x x_0) (= x! x_0) (= y y_0) (= y! y_0) (= tmp tmp!))))

(define-fun post-f ((i Int) (conf_0 Int) (x Int) (y Int) (tmp Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (i_4 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (x_0 Int) (y_0 Int)) Bool

    (or (not (and (= i i_2) (= conf_0 conf_0_1) (= x x_0) (= y y_0))) (not (and (>= i_2 x_0) (> 0 i_2) (not (>= i_2 y_0))))))





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
                