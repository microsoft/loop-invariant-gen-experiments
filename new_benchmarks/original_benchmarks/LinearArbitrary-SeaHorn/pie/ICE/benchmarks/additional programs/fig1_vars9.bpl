function {:existential true} b0(x:int, y:int, v1: int, v2: int, v3: int, v4: int, v5: int, v6: int, v7: int, v8: int, v9: int): bool;

var y: int;


procedure main()
modifies y;
{
  var x: int;
  var v1, v2, v3, v4, v5, v6, v7, v8, v9: int;

  x := -1;
  while (x < 0)
  invariant b0(x, y, v1, v2, v3, v4, v5, v6, v7, v8, v9);
  {
    x := x + y;
    y := y + 1;
    havoc v1;
    havoc v2;
    havoc v3;
    havoc v4;
    havoc v5;
    havoc v6;
    havoc v7;
    havoc v8;
    havoc v9;
  }
  assert y > 0;
}

