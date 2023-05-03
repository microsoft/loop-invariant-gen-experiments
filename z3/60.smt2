 (set-logic HORN)
     (declare-fun inv (Int Int) Bool)
     ; Initial condition
     (assert (forall ((c Int)(n Int)) (=> ( and (= c 0) (> n 0)) (inv c n))))
     ; Transition relation
     (assert (forall ((c Int)(n Int)(c1 Int)) (=> (and (inv c n) (or (and (not (= c n)) (= c1 (+ c 1))) (and (= c n) (= c1 1)))) (inv c1 n))))
     ; Property
     (assert (forall ((c Int)(n Int)) (=> (and (inv c n) (< c 0) (> c n)) (= c n))))
     (check-sat)
     (get-model)

Input:
Boogie
int main() {
  // variable declarations
  int c;
  int n;
  int v1;
  int v2;
  int v3;
  // pre-conditions
  (c = 0);
  assume((n > 0));
  // loop body
  while (unknown()) {
    {
      if ( unknown() ) {
        if ( (c != n) )
        {
        (c  = (c + 1));
        }
      } else {
        if ( (c == n) )
        {
        (c  = 1);
        }
      }

    }

  }
  // post-condition
if ( (c < 0) )
if ( (c > n) )
assert( (c == n) );

}

LoopInvariantGPT:
procedure main()
{
var c: int;
var n: int;
var nondet: bool;
// pre-conditions
c := 0;
assume(n > 0);
// loop body
havoc nondet;
while (nondet)
invariant 0 <= c && c <= n;
{
havoc nondet;
if (nondet) {
if (c != n) {
c := c + 1;
}
} else {
if (c == n) {
c := 1;
}
}
}
// post-condition
if (c < 0) {
if (c > n) {
assert(c == n);
}
}
}