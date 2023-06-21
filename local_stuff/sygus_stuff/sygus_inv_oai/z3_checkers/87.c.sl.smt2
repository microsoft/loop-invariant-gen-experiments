(set-logic LIA)

(define-fun inv-f ((lock Int) (x Int) (y Int) (tmp Int) (lock_0 Int) (lock_1 Int) (lock_2 Int) (lock_3 Int) (lock_4 Int) (lock_5 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (x_4 Int) (x_5 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int)) Bool (and (or (not (= lock lock_2)) (not (= x x_2)) (not (= y y_1)) (not (= x_2 y_1)) (= lock_2 1)) (<= lock 1)))



(define-fun pre-f ((lock Int) (x Int) (y Int) (tmp Int) (lock_0 Int) (lock_1 Int) (lock_2 Int) (lock_3 Int) (lock_4 Int) (lock_5 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (x_4 Int) (x_5 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int)) Bool

    (and (= lock lock_1) (= x x_1) (= y y_0) (= x_1 y_0) (= lock_1 1)))

(define-fun trans-f ((lock Int) (x Int) (y Int) (tmp Int) (lock_0 Int) (lock_1 Int) (lock_2 Int) (lock_3 Int) (lock_4 Int) (lock_5 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (x_4 Int) (x_5 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int) (lock! Int) (x! Int) (y! Int) (tmp! Int) (lock_0! Int) (lock_1! Int) (lock_2! Int) (lock_3! Int) (lock_4! Int) (lock_5! Int) (x_0! Int) (x_1! Int) (x_2! Int) (x_3! Int) (x_4! Int) (x_5! Int) (y_0! Int) (y_1! Int) (y_2! Int) (y_3! Int)) Bool

    (or (and (= lock_2 lock) (= x_2 x) (= y_1 y) (= lock_2 lock!) (= x_2 x!) (= y_1 y!) (= lock lock!) (= tmp tmp!)) (and (= lock_2 lock) (= x_2 x) (= y_1 y) (not (= x_2 y_1)) (= lock_3 1) (= x_3 y_1) (= lock_4 lock_3) (= x_4 x_3) (= y_2 y_1) (= lock_4 lock!) (= x_4 x!) (= y_2 y!) (= tmp tmp!)) (and (= lock_2 lock) (= x_2 x) (= y_1 y) (not (= x_2 y_1)) (= lock_5 0) (= x_5 y_1) (= y_3 (+ y_1 1)) (= lock_4 lock_5) (= x_4 x_5) (= y_2 y_3) (= lock_4 lock!) (= x_4 x!) (= y_2 y!) (= tmp tmp!))))

(define-fun post-f ((lock Int) (x Int) (y Int) (tmp Int) (lock_0 Int) (lock_1 Int) (lock_2 Int) (lock_3 Int) (lock_4 Int) (lock_5 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (x_4 Int) (x_5 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int)) Bool

    (or (not (and (= lock lock_2) (= x x_2) (= y y_1))) (not (and (not (not (= x_2 y_1))) (not (= lock_2 1))))))





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
                