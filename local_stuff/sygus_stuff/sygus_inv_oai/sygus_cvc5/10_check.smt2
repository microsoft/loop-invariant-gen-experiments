(set-logic LIA)

(define-fun inv-f ((x Int) (y Int) (tmp Int) (x_0 Int) (x_1 Int) (x_2 Int) (y_0 Int) (y_1 Int) (y_2 Int)) Bool (and (or (not (= x x_1)) (not (= y y_1)) (not (= y_1 0)) (not (= x_1 4))) (>= y 0)))

(define-fun pre-f ((x Int) (y Int) (tmp Int) (x_0 Int) (x_1 Int) (x_2 Int) (y_0 Int) (y_1 Int) (y_2 Int)) Bool
    (and (= x x_0) (= y y_0) (>= x_0 0) (<= x_0 2) (<= y_0 2) (>= y_0 0)))
(define-fun trans-f ((x Int) (y Int) (tmp Int) (x_0 Int) (x_1 Int) (x_2 Int) (y_0 Int) (y_1 Int) (y_2 Int) (x! Int) (y! Int) (tmp! Int) (x_0! Int) (x_1! Int) (x_2! Int) (y_0! Int) (y_1! Int) (y_2! Int)) Bool
    (or (and (= x_1 x) (= y_1 y) (= x_1 x!) (= y_1 y!) (= x x!) (= y y!) (= tmp tmp!)) (and (= x_1 x) (= y_1 y) (= x_2 (+ x_1 2)) (= y_2 (+ y_1 2)) (= x_2 x!) (= y_2 y!) (= tmp tmp!))))
(define-fun post-f ((x Int) (y Int) (tmp Int) (x_0 Int) (x_1 Int) (x_2 Int) (y_0 Int) (y_1 Int) (y_2 Int)) Bool
    (or (not (and (= x x_1) (= y y_1))) (not (and (= y_1 0) (not (not (= x_1 4)))))))

(assert (exists ((v1 Int)(v2 Int)(v3 Int)(v4 Int)(v5 Int)(v6 Int)(v7 Int)(v8 Int)(v9 Int))
    (not (=> 
        (pre-f v1 v2 v3 v4 v5 v6 v7 v8 v9) 
        (inv-f v1 v2 v3 v4 v5 v6 v7 v8 v9)
    ))
))
(assert (exists ((v1 Int)(v2 Int)(v3 Int)(v4 Int)(v5 Int)(v6 Int)(v7 Int)(v8 Int)(v9 Int)(v1! Int)(v2! Int)(v3! Int)(v4! Int)(v5! Int)(v6! Int)(v7! Int)(v8! Int)(v9! Int)) 
    (not (=>
        (and 
            (inv-f v1 v2 v3 v4 v5 v6 v7 v8 v9)
            (trans-f v1 v2 v3 v4 v5 v6 v7 v8 v9 v1! v2! v3! v4! v5! v6! v7! v8! v9!)
        )
        (inv-f v1! v2! v3! v4! v5! v6! v7! v8! v9!)
    ))
))
(assert (exists ((v1 Int)(v2 Int)(v3 Int)(v4 Int)(v5 Int)(v6 Int)(v7 Int)(v8 Int)(v9 Int))
    (not (=> 
        (inv-f v1 v2 v3 v4 v5 v6 v7 v8 v9) 
        (post-f v1 v2 v3 v4 v5 v6 v7 v8 v9)
    ))
))


(check-sat)