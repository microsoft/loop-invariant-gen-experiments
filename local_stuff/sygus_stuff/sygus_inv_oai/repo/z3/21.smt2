(set-logic HORN)
(declare-fun inv (Int Int Int Int) Bool)

; Initial condition
(assert (forall ((x Int) (m Int) (n Int)) (=> (and (= x 1) (= m 1)) (inv x m n 1))))

; Transition relation
(assert (forall ((x Int) (m Int) (n Int) (x1 Int) (m1 Int)) (=> (and (inv x m n 1) (< x n) (ite (unknown) (= m1 x) (= m1 m)) (= x1 (+ x 1))) (inv x1 m1 n 1))))

; Property
(assert (forall ((x Int) (m Int) (n Int)) (=> (and (inv x m n 1) (not (< x n)) (> n 1)) (< m n))))

(check-sat)
(get-model)

; Boogie program
procedure main()
{
  var x: int;
  var m: int;
  var n: int;
  var nondet: bool;
  // Initial conditions
  x := 1;
  m := 1;
  // loop body
  havoc nondet;
  while (x < n)
  invariant 1 <= m && m <= x;
  {
    havoc nondet;
    if (nondet) {
      m := x;
    }
    x := x + 1;
  }
  // post-condition
  if (n > 1) {
    assert(m < n);
    //assert(m >= 1);
  }
}