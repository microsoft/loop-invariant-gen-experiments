procedure main()
{
  var x: int;
  var y: int;
  // variable initialization
  x := 1;
  // loop body
  while (x <= 10)
  invariant 1 <= x && x <= 11;
  invariant y == 10 - x;
  {
    y := 10 - x;
    x := x + 1;
  }
  // post-condition
  assert(y < 10);
}