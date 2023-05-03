 (set-logic HORN)
     (declare-fun inv (Int Int Int Int) Bool)
     ; Initial condition
     (assert (forall ((i Int)(j Int)(x Int)(y Int)) (=> ( and (= i 0) (= j 0) (= y 1)) (inv i j x y))))
     ; Transition relation
     (assert (forall ((i Int)(j Int)(x Int)(y Int)(i1 Int)(j1 Int)) (=> (and (inv i j x y) (<= i x) (= i1 (+ i 1)) (= j1 (+ j y)) ) (inv i1 j1 x y))))
     ; Property
     (assert (forall ((i Int)(j Int)(x Int)(y Int)) (=> (and (inv i j x y)(not (<= i x))) (=> (not (= i j)) (not (= y 1))) )))
     (check-sat)
     (get-model)