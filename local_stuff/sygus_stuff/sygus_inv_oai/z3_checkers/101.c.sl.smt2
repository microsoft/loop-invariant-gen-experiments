(set-logic LIA)

(define-fun inv-f ((n Int) (x Int) (n_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int)) Bool (and (or (not (= n n_0)) (not (= x x_2)) (>= x_2 n_0) (<= n_0 0)) (<= x n)))



(define-fun pre-f ((n Int) (x Int) (n_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int)) Bool

    (and (= x x_1) (= x_1 0)))

(define-fun trans-f ((n Int) (x Int) (n_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (n! Int) (x! Int) (n_0! Int) (x_0! Int) (x_1! Int) (x_2! Int) (x_3! Int)) Bool

    (or (and (= x_2 x) (= x_2 x!) (= n n_0) (= n! n_0)) (and (= x_2 x) (< x_2 n_0) (= x_3 (+ x_2 1)) (= x_3 x!) (= n n_0) (= n! n_0))))

(define-fun post-f ((n Int) (x Int) (n_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int)) Bool

    (or (not (and (= n n_0) (= x x_2))) (not (and (not (< x_2 n_0)) (not (= x_2 n_0)) (not (< n_0 0))))))





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

(assert
    (or
        (not (=> 
            (pre-f v0 v1 v2 v3 v4 v5 v6 ) 
            (inv-f v0 v1 v2 v3 v4 v5 v6 )
        ))


        (not (=>
            (and 
                (inv-f v0 v1 v2 v3 v4 v5 v6 )
                (trans-f v0 v1 v2 v3 v4 v5 v6  v0! v1! v2! v3! v4! v5! v6! )
            )
            (inv-f v0! v1! v2! v3! v4! v5! v6! )
        ))


        (not (=> 
            (inv-f v0 v1 v2 v3 v4 v5 v6 ) 
            (post-f v0 v1 v2 v3 v4 v5 v6 )
        ))
    )
)

(check-sat)
                