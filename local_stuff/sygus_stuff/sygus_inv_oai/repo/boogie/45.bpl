procedure main()
{
  var c: int;
  var n: int;
  var nondet: bool;
  var nondet_if: bool;
  // pre-conditions
  c := 0;
  assume(n > 0);
  // loop body
  havoc nondet;
  while (nondet)
  invariant 0 <= c && c <= n;
  {
    havoc nondet;
    havoc nondet_if;
    if (nondet_if) {
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
  if (c != n) {
    assert(c >= 0);
  }
}