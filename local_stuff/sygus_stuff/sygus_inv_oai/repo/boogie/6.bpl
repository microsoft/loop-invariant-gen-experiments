procedure main()
{
  var v1, v2, v3: int;
  var x: int;
  var size: int;
  var y, z: int;
  var nondet: bool;

  // loop body
  havoc nondet;
  while (x < size)
  invariant 0 <= x && x <= size;
  invariant (x == 0) || (z >= y);
  {
    havoc nondet;
    x := x + 1;
    if (z <= y) {
      y := z;
    }
  }

  // post-condition
  if (size > 0) {
    assert(z >= y);
  }
}