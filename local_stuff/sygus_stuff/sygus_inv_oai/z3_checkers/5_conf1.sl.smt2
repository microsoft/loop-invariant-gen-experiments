(set-logic LIA)

(define-fun inv-f ((conf_0 Int) (size Int) (x Int) (y Int) (z Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (size_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int) (z_0 Int)) Bool (and (or (not (= conf_0 conf_0_1)) (not (= size size_0)) (not (= x x_2)) (not (= y y_1)) (not (= z z_0)) (>= x_2 size_0) (not (>= size_0 1)) (>= z_0 y_1)) (<= x size_0)))



(define-fun pre-f ((conf_0 Int) (size Int) (x Int) (y Int) (z Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (size_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int) (z_0 Int)) Bool

    (and (= conf_0 conf_0_0) (= x x_1) (= conf_0_0 7) (= x_1 0)))

(define-fun trans-f ((conf_0 Int) (size Int) (x Int) (y Int) (z Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (size_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int) (z_0 Int) (conf_0! Int) (size! Int) (x! Int) (y! Int) (z! Int) (conf_0_0! Int) (conf_0_1! Int) (conf_0_2! Int) (conf_0_3! Int) (conf_0_4! Int) (size_0! Int) (x_0! Int) (x_1! Int) (x_2! Int) (x_3! Int) (y_0! Int) (y_1! Int) (y_2! Int) (y_3! Int) (z_0! Int)) Bool

    (or (and (= conf_0_1 conf_0) (= x_2 x) (= y_1 y) (= conf_0_1 conf_0!) (= x_2 x!) (= y_1 y!) (= size size_0) (= size! size_0) (= conf_0 conf_0!) (= y y!) (= z z!)) (and (= conf_0_1 conf_0) (= x_2 x) (= y_1 y) (< x_2 size_0) (= x_3 (+ x_2 1)) (= conf_0_2 (- conf_0_1 381)) (<= z_0 y_1) (= y_2 z_0) (= conf_0_3 (- conf_0_2 637)) (= conf_0_4 conf_0_3) (= y_3 y_2) (= conf_0_4 conf_0!) (= x_3 x!) (= y_3 y!) (= size size_0) (= size! size_0) (= z z_0) (= z! z_0)) (and (= conf_0_1 conf_0) (= x_2 x) (= y_1 y) (< x_2 size_0) (= x_3 (+ x_2 1)) (= conf_0_2 (- conf_0_1 381)) (not (<= z_0 y_1)) (= conf_0_4 conf_0_2) (= y_3 y_1) (= conf_0_4 conf_0!) (= x_3 x!) (= y_3 y!) (= size size_0) (= size! size_0) (= z z_0) (= z! z_0))))

(define-fun post-f ((conf_0 Int) (size Int) (x Int) (y Int) (z Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (size_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int) (z_0 Int)) Bool

    (or (not (and (= conf_0 conf_0_1) (= size size_0) (= x x_2) (= y y_1) (= z z_0))) (not (and (not (< x_2 size_0)) (> size_0 0) (not (>= z_0 y_1))))))





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
                