procedure main()
{
  var c: int;
  var n: int;
  var nondet: bool;
  var cond: bool;
  // pre-conditions
  c := 0;
  assume(n > 0);
  // loop body
  havoc nondet;
  while (nondet)
  invariant c >= 0 && c <= n + 1;
  {
    havoc nondet;
    havoc cond;
    if (cond) {
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
  if (c == n) {
    assert(n > -1);
  }
}