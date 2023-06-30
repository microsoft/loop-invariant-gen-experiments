function {:existential true} b0(x:int, y:int, i:int, j:int): bool;

var i, j: int;

procedure main()
{
  var x, y: int;
  x := i;
  y := j;

  while (x != 0)
  invariant b0(x, y, i, j);
  {
    x := x - 1;
    y := y - 1;
  }
  if (i == j)
  {
    assert y == 0;
  }
}

