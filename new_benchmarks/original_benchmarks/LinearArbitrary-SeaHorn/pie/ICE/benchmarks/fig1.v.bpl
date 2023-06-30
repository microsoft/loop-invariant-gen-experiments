function {:existential true} b0(x:int, y:int, v1: int, v2: int, v3: int): bool;

var y: int;


procedure main()
modifies y;
{
  var x: int;
  var v1, v2, v3: int;

  x := -1;
  while (x < 0)
  invariant b0(x, y, v1, v2, v3);
  {
    x := x + y;
    y := y + 1;
    havoc v1;
    havoc v2;
    havoc v3;
  }
  assert y > 0;
}

