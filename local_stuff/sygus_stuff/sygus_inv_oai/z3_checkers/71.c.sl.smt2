(set-logic LIA)

(define-fun inv-f ((c Int) (y Int) (z Int) (tmp Int) (c_0 Int) (c_1 Int) (c_2 Int) (c_3 Int) (c_4 Int) (y_0 Int) (z_0 Int) (z_1 Int) (z_2 Int) (z_3 Int) (z_4 Int)) Bool (and (or (not (= c c_2)) (not (= y y_0)) (not (= z z_2)) (>= c_2 36) (>= z_2 0)) (<= c 36)))



(define-fun pre-f ((c Int) (y Int) (z Int) (tmp Int) (c_0 Int) (c_1 Int) (c_2 Int) (c_3 Int) (c_4 Int) (y_0 Int) (z_0 Int) (z_1 Int) (z_2 Int) (z_3 Int) (z_4 Int)) Bool

    (and (= c c_1) (= y y_0) (= z z_1) (= c_1 0) (>= y_0 0) (>= y_0 127) (= z_1 (* 36 y_0))))

(define-fun trans-f ((c Int) (y Int) (z Int) (tmp Int) (c_0 Int) (c_1 Int) (c_2 Int) (c_3 Int) (c_4 Int) (y_0 Int) (z_0 Int) (z_1 Int) (z_2 Int) (z_3 Int) (z_4 Int) (c! Int) (y! Int) (z! Int) (tmp! Int) (c_0! Int) (c_1! Int) (c_2! Int) (c_3! Int) (c_4! Int) (y_0! Int) (z_0! Int) (z_1! Int) (z_2! Int) (z_3! Int) (z_4! Int)) Bool

    (or (and (= c_2 c) (= z_2 z) (= c_2 c!) (= z_2 z!) (= c c!) (= y y!) (= z z!) (= tmp tmp!)) (and (= c_2 c) (= z_2 z) (< c_2 36) (= z_3 (+ z_2 1)) (= c_3 (+ c_2 1)) (= c_4 c_3) (= z_4 z_3) (= c_4 c!) (= z_4 z!) (= y y_0) (= y! y_0) (= tmp tmp!)) (and (= c_2 c) (= z_2 z) (not (< c_2 36)) (= c_4 c_2) (= z_4 z_2) (= c_4 c!) (= z_4 z!) (= y y_0) (= y! y_0) (= tmp tmp!))))

(define-fun post-f ((c Int) (y Int) (z Int) (tmp Int) (c_0 Int) (c_1 Int) (c_2 Int) (c_3 Int) (c_4 Int) (y_0 Int) (z_0 Int) (z_1 Int) (z_2 Int) (z_3 Int) (z_4 Int)) Bool

    (or (not (and (= c c_2) (= y y_0) (= z z_2))) (not (and (< c_2 36) (not (>= z_2 0))))))





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
                