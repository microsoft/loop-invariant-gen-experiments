(set-logic LIA)

; temp = 0.7 (define-fun inv-f ((x Int) (y Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int)) Bool (and (or (not (= x x_2)) (not (= y y_2)) (>= y_2 100000) (>= (- x_2 y_2) 0)) (<= y 100000)))
; temp = 0.2 (define-fun inv-f ((x Int) (y Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int)) Bool (and (or (not (= x x_2)) (not (= y y_2)) (>= y_2 100000) (>= x_2 y_2)) (<= y 100000)))
; output by cvc5 (define-fun inv-f ((x Int) (y Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int)) Bool (and (or (not (= x x_2)) (not (= y y_2)) (not (>= y_2 100000)) (>= (+ x_2 (* (- 1) y_2)) 0)) (>= x 1) (>= y 0)))

(define-fun pre-f ((x Int) (y Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int)) Bool
    (and (= x x_1) (= y y_1) (= x_1 1) (= y_1 0)))
(define-fun trans-f ((x Int) (y Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int) (x! Int) (y! Int) (x_0! Int) (x_1! Int) (x_2! Int) (x_3! Int) (y_0! Int) (y_1! Int) (y_2! Int) (y_3! Int)) Bool
    (or (and (= x_2 x) (= y_2 y) (= x_2 x!) (= y_2 y!) (= x x!)) (and (= x_2 x) (= y_2 y) (< y_2 100000) (= x_3 (+ x_2 y_2)) (= y_3 (+ y_2 1)) (= x_3 x!) (= y_3 y!))))
(define-fun post-f ((x Int) (y Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int)) Bool
    (or (not (and (= x x_2) (= y y_2))) (not (and (not (< y_2 100000)) (not (>= x_2 y_2))))))

(assert (exists ((v1 Int)(v2 Int)(v3 Int)(v4 Int)(v5 Int)(v6 Int)(v7 Int)(v8 Int)(v9 Int)(v10 Int))
    (not (=> 
        (pre-f v1 v2 v3 v4 v5 v6 v7 v8 v9 v10) 
        (inv-f v1 v2 v3 v4 v5 v6 v7 v8 v9 v10)
    ))
))
(assert (exists ((v1 Int)(v2 Int)(v3 Int)(v4 Int)(v5 Int)(v6 Int)(v7 Int)(v8 Int)(v9 Int)(v10 Int)(v1! Int)(v2! Int)(v3! Int)(v4! Int)(v5! Int)(v6! Int)(v7! Int)(v8! Int)(v9! Int)(v10! Int)) 
    (not (=>
        (and 
            (inv-f v1 v2 v3 v4 v5 v6 v7 v8 v9 v10)
            (trans-f v1 v2 v3 v4 v5 v6 v7 v8 v9 v10! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10!)
        )
        (inv-f v1! v2! v3! v4! v5! v6! v7! v8! v9! v10!)
    ))
))
(assert (exists ((v1 Int)(v2 Int)(v3 Int)(v4 Int)(v5 Int)(v6 Int)(v7 Int)(v8 Int)(v9 Int)(v10 Int))
    (not (=> 
        (inv-f v1 v2 v3 v4 v5 v6 v7 v8 v9 v10) 
        (post-f v1 v2 v3 v4 v5 v6 v7 v8 v9 v10)
    ))
))


(check-sat)