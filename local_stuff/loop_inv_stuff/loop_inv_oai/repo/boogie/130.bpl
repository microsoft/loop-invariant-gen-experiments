procedure main()
{
  var d1: int := 1;
  var d2: int := 1;
  var d3: int := 1;
  var x1: int := 1;
  var x2: int;
  var x3: int;

  while (x1 > 0)
  invariant x1 <= x2 && x1 <= x3;
  {
    if (x2 > 0) {
      if (x3 > 0) {
        x1 := x1 - d1;
        x2 := x2 - d2;
        x3 := x3 - d3;
      }
    }
  }

  assert(x2 >= 0);
  //assert(x3 >= 0);
}