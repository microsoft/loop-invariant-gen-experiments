procedure main()
{
  var c: int;
  var n: int;
  var v1: int;
  var v2: int;
  var v3: int;
  var nondet: bool;
  var nondet1: bool;
  // pre-conditions
  c := 0;
  assume(n > 0);
  // loop body
  havoc nondet;
  while (nondet)
  invariant 0 <= c && c <= n;
  {
    havoc nondet;
    havoc nondet1;
    if (nondet1) {
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
  if (c == n) {
    assert(n <= -1);
  }
}