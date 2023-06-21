procedure main()
{
  var n: int;
  var x: int;
  // pre-conditions
  assume(x == n);
  // loop body
  while (x > 0)
  invariant x >= 0;
  {
    x := x - 1;
  }
  // post-condition
  if (n >= 0) {
    assert(x == 0);
  }
}