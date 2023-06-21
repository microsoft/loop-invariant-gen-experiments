procedure main()
{
  var n: int;
  var x: int;
  var y: int;
  // variable declarations and initialization
  x := 1;
  // loop body
  while (x <= n)
  invariant 0 <= x && x <= n+1;
  invariant y == n - x + 1;
  {
    y := n - x;
    x := x + 1;
  }
  // post-condition
  if (n > 0) {
    //assert(y >= 0);
    assert(y < n);
  }
}