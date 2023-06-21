procedure main()
{
  var x: int;
  var y: int;
  var z: int;
  // initialization
  x := 0;
  // loop body
  while (x < 5)
  invariant 0 <= x && x <= 5;
  invariant z >= y;
  {
    x := x + 1;
    if (z <= y) {
      y := z;
    }
  }
  // post-condition
  assert(z >= y);
}