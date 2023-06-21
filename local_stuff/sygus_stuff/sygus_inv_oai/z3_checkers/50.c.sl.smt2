(set-logic LIA)

(define-fun inv-f ((c Int) (tmp Int) (c_0 Int) (c_1 Int) (c_2 Int) (c_3 Int) (c_4 Int) (c_5 Int)) Bool (or (not (= c c_2)) (>= c_2 0) (= c_2 4)))



(define-fun pre-f ((c Int) (tmp Int) (c_0 Int) (c_1 Int) (c_2 Int) (c_3 Int) (c_4 Int) (c_5 Int)) Bool

    (and (= c c_1) (= c_1 0)))

(define-fun trans-f ((c Int) (tmp Int) (c_0 Int) (c_1 Int) (c_2 Int) (c_3 Int) (c_4 Int) (c_5 Int) (c! Int) (tmp! Int) (c_0! Int) (c_1! Int) (c_2! Int) (c_3! Int) (c_4! Int) (c_5! Int)) Bool

    (or (and (= c_2 c) (= c_2 c!) (= c c!) (= tmp tmp!)) (and (= c_2 c) (not (= c_2 4)) (= c_3 (+ c_2 1)) (= c_4 c_3) (= c_4 c!) (= tmp tmp!)) (and (= c_2 c) (not (not (= c_2 4))) (= c_4 c_2) (= c_4 c!) (= tmp tmp!)) (and (= c_2 c) (= c_2 4) (= c_5 1) (= c_4 c_5) (= c_4 c!) (= tmp tmp!)) (and (= c_2 c) (not (= c_2 4)) (= c_4 c_2) (= c_4 c!) (= tmp tmp!))))

(define-fun post-f ((c Int) (tmp Int) (c_0 Int) (c_1 Int) (c_2 Int) (c_3 Int) (c_4 Int) (c_5 Int)) Bool

    (or (not (= c c_2)) (not (and (not (= c_2 4)) (not (>= c_2 0))))))





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

(assert
    (or
        (not (=> 
            (pre-f v0 v1 v2 v3 v4 v5 v6 v7 ) 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 )
        ))


        (not (=>
            (and 
                (inv-f v0 v1 v2 v3 v4 v5 v6 v7 )
                (trans-f v0 v1 v2 v3 v4 v5 v6 v7  v0! v1! v2! v3! v4! v5! v6! v7! )
            )
            (inv-f v0! v1! v2! v3! v4! v5! v6! v7! )
        ))


        (not (=> 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 ) 
            (post-f v0 v1 v2 v3 v4 v5 v6 v7 )
        ))
    )
)

(check-sat)
                