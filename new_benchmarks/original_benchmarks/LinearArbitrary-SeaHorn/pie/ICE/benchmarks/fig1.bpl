function {:existential true} b0(x:int, y:int): bool;

var y: int;


procedure main()
modifies y;
{
  var x: int;
  x := -1;
  while (x < 0)
  invariant b0(x, y);
  {
    x := x + y;
    y := y + 1;
  }
  assert y > 0;
}

