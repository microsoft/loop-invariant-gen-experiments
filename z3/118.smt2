 (set-logic HORN)
     (declare-fun inv (Int Int Int) Bool)
     ; Initial condition
     (assert (forall ((i Int)(sn Int)(size Int)) (=> ( and (= sn 0) (= i 1)) (inv i sn size))))
     ; Transition relation
     (assert (forall ((i Int)(sn Int)(size Int)(i1 Int)(sn1 Int)) (=> (and (inv i sn size) (<= i size) (= i1 (+ i 1)) (= sn1 (+ sn 1)) ) (inv i1 sn1 size))))
     ; Property
     (assert (forall ((i Int)(sn Int)(size Int)) (=> (and (inv i sn size)(not (<= i size))) (or (= sn size) (= sn 0)) )))
     (check-sat)
     (get-model)