procedure main()
{
  var z1, z2, z3: int;
  var x, m, n: int;
  var nondet: bool;

  x := 1;
  m := 1;

  havoc n;

  // loop body
  havoc nondet;
  while (x < n)
  invariant x >= 1 && m >= 1;
  {
    havoc nondet;
    if (nondet) {
      m := x;
    }
    x := x + 1;
  }

  if (n > 1) {
    // assert (m < n);
    assert (m >= 1);
  }
}