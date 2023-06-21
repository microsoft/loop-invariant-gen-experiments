procedure main()
{
  var z1, z2, z3: int;
  var x, m, n: int;
  var nondet: bool;

  x := 0;
  m := 0;

  havoc nondet;
  while (x < n)
  invariant 0 <= x && x <= n && (x <= m || m == 0);
  {
    havoc nondet;
    if (nondet) {
      m := x;
    }
    x := x + 1;
  }

  if (n > 0) {
    assert(m < n);
    //assert(m >= 0);
  }
}