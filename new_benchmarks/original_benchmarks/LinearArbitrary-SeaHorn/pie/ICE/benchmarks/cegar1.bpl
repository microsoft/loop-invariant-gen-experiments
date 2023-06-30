function {:existential true} b0(x:int, y:int): bool;

var x, y: int;


procedure main()
modifies x, y;
{
  assume 0 <= x && x <= 2;
  assume 0 <= y && y <= 2;
  while (*)
  invariant b0(x, y);
  {
    x := x + 2;
    y := y + 2;
  }
  assert (!((x == 4) && (y == 0)));
}

