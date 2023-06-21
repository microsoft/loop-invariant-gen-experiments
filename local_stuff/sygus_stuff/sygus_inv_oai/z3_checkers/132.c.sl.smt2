(set-logic LIA)

(define-fun inv-f ((c Int) (i Int) (j Int) (t Int) (tmp Int) (c_0 Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (j_0 Int) (j_1 Int) (j_2 Int) (j_3 Int) (t_0 Int) (t_1 Int) (t_2 Int) (t_3 Int)) Bool (and (or (not (= c c_0)) (not (= i i_1)) (not (= j j_1)) (not (= t t_1)) (>= i_1 0)) (>= i 0)))



(define-fun pre-f ((c Int) (i Int) (j Int) (t Int) (tmp Int) (c_0 Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (j_0 Int) (j_1 Int) (j_2 Int) (j_3 Int) (t_0 Int) (t_1 Int) (t_2 Int) (t_3 Int)) Bool

    (and (= i i_0) (= i_0 0)))

(define-fun trans-f ((c Int) (i Int) (j Int) (t Int) (tmp Int) (c_0 Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (j_0 Int) (j_1 Int) (j_2 Int) (j_3 Int) (t_0 Int) (t_1 Int) (t_2 Int) (t_3 Int) (c! Int) (i! Int) (j! Int) (t! Int) (tmp! Int) (c_0! Int) (i_0! Int) (i_1! Int) (i_2! Int) (i_3! Int) (j_0! Int) (j_1! Int) (j_2! Int) (j_3! Int) (t_0! Int) (t_1! Int) (t_2! Int) (t_3! Int)) Bool

    (or (and (= i_1 i) (= j_1 j) (= t_1 t) (= i_1 i!) (= j_1 j!) (= t_1 t!) (= c c!) (= i i!) (= j j!) (= t t!) (= tmp tmp!)) (and (= i_1 i) (= j_1 j) (= t_1 t) (> c_0 48) (< c_0 57) (= j_2 (+ i_1 i_1)) (= t_2 (- c_0 48)) (= i_2 (+ j_2 t_2)) (= i_3 i_2) (= j_3 j_2) (= t_3 t_2) (= i_3 i!) (= j_3 j!) (= t_3 t!) (= c c_0) (= c! c_0) (= tmp tmp!)) (and (= i_1 i) (= j_1 j) (= t_1 t) (> c_0 48) (not (< c_0 57)) (= i_3 i_1) (= j_3 j_1) (= t_3 t_1) (= i_3 i!) (= j_3 j!) (= t_3 t!) (= c c_0) (= c! c_0) (= tmp tmp!)) (and (= i_1 i) (= j_1 j) (= t_1 t) (not (> c_0 48)) (= i_3 i_1) (= j_3 j_1) (= t_3 t_1) (= i_3 i!) (= j_3 j!) (= t_3 t!) (= c c_0) (= c! c_0) (= tmp tmp!))))

(define-fun post-f ((c Int) (i Int) (j Int) (t Int) (tmp Int) (c_0 Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (j_0 Int) (j_1 Int) (j_2 Int) (j_3 Int) (t_0 Int) (t_1 Int) (t_2 Int) (t_3 Int)) Bool

    (or (not (and (= c c_0) (= i i_1) (= j j_1) (= t t_1))) (not (not (>= i_1 0)))))





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

(assert
    (or
        (not (=> 
            (pre-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 ) 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 )
        ))


        (not (=>
            (and 
                (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 )
                (trans-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17  v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! v12! v13! v14! v15! v16! v17! )
            )
            (inv-f v0! v1! v2! v3! v4! v5! v6! v7! v8! v9! v10! v11! v12! v13! v14! v15! v16! v17! )
        ))


        (not (=> 
            (inv-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 ) 
            (post-f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 )
        ))
    )
)

(check-sat)
                