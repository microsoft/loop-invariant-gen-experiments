procedure main()
{
  var x: int;
  var y: int;
  // variable initialization
  x := 1;
  // loop body
  while (x <= 100)
  invariant 0 <= y && y <= 100;
  {
    y := 100 - x;
    x := x + 1;
  }
  // post-condition
  assert(y >= 0);
  //assert(y < 100);
}