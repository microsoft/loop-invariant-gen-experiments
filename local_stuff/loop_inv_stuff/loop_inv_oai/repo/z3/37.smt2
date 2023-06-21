(set-logic HORN)
(declare-fun inv (Int) Bool)

; Initial condition
(assert (forall ((c Int)) (=> (= c 0) (inv c))))

; Transition relation
(assert (forall ((c Int) (c1 Int) (nondet Bool) (nondet2 Bool))
  (=> (and (inv c)
           (ite nondet
             (ite nondet2
               (and (not (= c 40)) (= c1 (+ c 1)))
               (= c1 c))
             (ite (= c 40) (= c1 1) (= c1 c))))
       (inv c1))))

; Property
(assert (forall ((c Int))
  (=> (and (inv c) (not (< c 0)) (not (> c 40))) (= c 40))))

(check-sat)
(get-model)

procedure main()
{
  var c: int;
  var nondet: bool;
  var nondet2: bool;
  // pre-conditions
  assume(c = 0);
  // loop body
  havoc nondet;
  while (nondet)
  invariant 0 <= c && c <= 40;
  {
    havoc nondet;
    havoc nondet2;
    if (nondet2) {
      if (c != 40) {
        c := c + 1;
      }
    } else {
      if (c == 40) {
        c := 1;
      }
    }
  }
  // post-condition
  if (c < 0 || c > 40) {
    assert(c == 40);
  }
}