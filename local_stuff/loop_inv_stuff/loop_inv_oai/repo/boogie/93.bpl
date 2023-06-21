procedure main()
{
  var i: int;
  var n: int;
  var x: int;
  var y: int;
  var nondet: bool;
  // pre-conditions
  assume(n >= 0);
  i := 0;
  x := 0;
  y := 0;
  // loop body
  while (i < n)
  invariant 0 <= i && i <= n;
  invariant 3 * i == x + y;
  {
    i := i + 1;
    havoc nondet;
    if (nondet) {
      x := x + 1;
      y := y + 2;
    } else {
      x := x + 2;
      y := y + 1;
    }
  }
  // post-condition
  assert(3 * n == x + y);
}