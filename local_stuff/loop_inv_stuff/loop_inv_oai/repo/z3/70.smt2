(set-logic HORN)
(declare-fun inv (Int Int Int) Bool)

; Initial condition
(assert (forall ((n Int) (x Int) (y Int)) (=> (and (= x 1)) (inv n x y))))

; Transition relation
(assert (forall ((n Int) (x Int) (y Int) (x1 Int) (y1 Int))
  (=> (and (inv n x y) (<= x n) (= x1 (+ x 1)) (= y1 (- n x)))
      (inv n x1 y1))))

; Property
(assert (forall ((n Int) (x Int) (y Int))
  (=> (and (inv n x y) (not (<= x n)) (> n 0))
      (and (>= y 0) (< y n)))))

(check-sat)
(get-model)

Boogie:

procedure main()
{
  var n: int;
  var x: int;
  var y: int;
  // loop body
  x := 1;
  while (x <= n)
  invariant x >= 1 && x - 1 <= n;
  {
    y := n - x;
    x := x + 1;
  }
  // post-condition
  if (n > 0) {
    //assert(y >= 0);
    assert(y < n);
  }
}