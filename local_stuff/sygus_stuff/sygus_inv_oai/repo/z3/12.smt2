(set-logic HORN)
(declare-fun inv (Int Int) Bool)

; Initial condition 
(assert (forall ((x Int)(y Int)) (=> (and (>= x 0) (<= x 10) (<= y 10) (>= y 0)) (inv x y))))

; Transition relation 
(assert (forall ((x Int)(y Int)(x1 Int)(y1 Int)) (=> (and (inv x y) (= x1 (+ x 10)) (= y1 (+ y 10))) (inv x1 y1))))

; Property
(assert (forall ((x Int)(y Int)) (=> (and (inv x y) (= y 0)) (not (= x 20)))))

(check-sat)
(get-model)

 

procedure main()
{
  var x: int;
  var y: int;
  var nondet: bool;
  // pre-conditions
  assume(0 <= x);
  assume(x <= 10);
  assume(y <= 10);
  assume(y >= 0);
  // loop body
  havoc nondet;
  while (nondet)
  invariant x - y <= 10 && y - x <= 10;
  {
    havoc nondet;
    x := x + 10;
    y := y + 10;
  }
  // post-condition
  if(y==0) {
    assert(x != 20);
  }
}