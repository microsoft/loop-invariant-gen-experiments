procedure main()
{
  var c: int;
  var n: int;
  var nondet1: bool;
  var nondet2: bool;
  // pre-conditions
  c := 0;
  assume(n > 0);
  // loop body
  havoc nondet1;
  while (nondet1)
  invariant 0 <= c && c <= n;
  {
    havoc nondet1;
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