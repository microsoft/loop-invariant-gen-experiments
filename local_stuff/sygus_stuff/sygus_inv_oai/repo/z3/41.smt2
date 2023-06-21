(set-logic HORN)
(declare-fun inv (Int Int) Bool)

; Initial condition
(assert (forall ((c Int)(n Int)) (=> (and (= c 0) (> n 0)) (inv c n))))

; Transition relation
(assert (forall ((c Int)(n Int)(c1 Int)) (=> (and (inv c n) (or (and (> c n) (= c1 (+ c 1))) (and (= c n) (= c1 1)))) (inv c1 n))))

; Property
(assert (forall ((c Int)(n Int)) (=> (and (inv c n) (not (= c n))) (<= c n))))

(check-sat)
(get-model)

 

procedure main()
{
  var c: int;
  var n: int;
  var nondet: bool;
  var nondet2: bool;
  // pre-conditions
  c := 0;
  assume(n > 0);
  // loop body
  havoc nondet;
  while (nondet)
  invariant 0 <= c && c <= n+1;
  {
    havoc nondet;
    havoc nondet2;
    if (nondet2) {
      if (c > n) {
        c := c + 1;
      }
    } else {
      if (c == n) {
        c := 1;
      }
    }
  }
  // post-condition
  if (c != n) {
    assert(c <= n);
  }
}