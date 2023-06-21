procedure main()
{
  var x: int;
  var y: int;
  // pre-conditions
  assume(x == -50);
  // loop body
  while (x < 0)
  invariant x + y >= -50;
  invariant y >= 0;
  {
    x := x + y;
    y := y + 1;
  }
  // post-condition
  assert(y > 0);
}