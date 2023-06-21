procedure main()
{
  var n: int;
  var y: int;
  var x: int := 1;

  while (x <= n)
  invariant 0 <= x && x <= n + 1;
  invariant y == n - x + 1;
  {
    y := n - x;
    x := x + 1;
  }

  if (n > 0) {
    assert(y >= 0);
    //assert(y <= n);
  }
}