function {:existential true} b0(x:int, y:int, v1: int, v2: int, v3: int): bool;

var x, y: int;


procedure main()
modifies x, y;
{
  var v1, v2, v3: int;

  assume 0 <= x && x <= 2;
  assume 0 <= y && y <= 2;
  while (*)
  invariant b0(x, y, v1, v2, v3);
  {
    x := x + 2;
    y := y + 2;
    havoc v1;
    havoc v2;
    havoc v3;
  }
  assert (!((x == 4) && (y == 0)));
}

