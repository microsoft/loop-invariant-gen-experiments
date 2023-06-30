function {:existential true} b0(x:int, y:int, i:int, j:int, v1: int, v2: int, v3: int): bool;

var i, j: int;

procedure main()
{
  var x, y: int;
  var v1, v2, v3: int;

  x := i;
  y := j;

  while (x != 0)
  invariant b0(x, y, i, j, v1, v2, v3);
  {
    x := x - 1;
    y := y - 1;
    havoc v1;
    havoc v2;
    havoc v3;
  }
  if (i == j)
  {
    assert y == 0;
  }
}

