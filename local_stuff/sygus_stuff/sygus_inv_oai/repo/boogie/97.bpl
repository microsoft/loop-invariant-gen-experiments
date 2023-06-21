procedure main()
{
  var i: int;
  var j: int;
  var x: int;
  var y: int;
  // pre-conditions
  j := 0;
  i := 0;
  y := 2;
  // loop body
  while (i <= x)
  invariant i <= x + 1;
  invariant j == i * y;
  {
    i := i + 1;
    j := j + y;
  }
  // post-condition
  if (y == 1) {
    assert(i == j);
  }
}