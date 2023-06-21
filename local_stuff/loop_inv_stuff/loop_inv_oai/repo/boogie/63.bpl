procedure main()
{
  var x: int;
  var y: int;
  // Initialization
  x := 1;
  // loop body
  while (x <= 10)
  invariant 1 <= x && x <= 11;
  invariant y == 10 - x + 1;
  {
    y := 10 - x;
    x := x + 1;
  }
  // post-condition
  assert(y >= 0);
  //assert(y < 10);
}