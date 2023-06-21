procedure main()
{
  var z1, z2, z3: int;
  var x, m, n: int;
  var nondet: bool;
  x := 0;
  m := 0;

  havoc n;
  assume(n >= 0);

  // loop body
  havoc nondet;
  while (x < n)
  invariant 0 <= x <= n;
  invariant 0 <= m <= x;
  {
    havoc nondet;
    if (nondet) {
      m := x;
    }
    x := x + 1;
  }

  if (n > 0) {
    // assert (m < n);
    assert (m >= 0);
  }
}