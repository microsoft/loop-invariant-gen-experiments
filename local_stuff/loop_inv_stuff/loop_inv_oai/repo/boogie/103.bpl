procedure main()
{
  var x: int;
  // pre-conditions
  assume(x == 0);
  // loop body
  while (x < 100)
  invariant 0 <= x && x <= 100;
  {
    x := x + 1;
  }
  // post-condition
  assert(x == 100);
}