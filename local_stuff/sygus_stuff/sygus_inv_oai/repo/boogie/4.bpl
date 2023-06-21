procedure main()
{
  var x: int;
  var y: int;
  var z: int;
  // initialization
  x := 0;
  // loop body
  while (x < 500)
  invariant 0 <= x && x <= 500;
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