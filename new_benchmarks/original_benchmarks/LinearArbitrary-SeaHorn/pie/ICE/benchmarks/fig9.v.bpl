function {:existential true} b0(x:int, y:int, v1: int, v2: int, v3: int): bool;

procedure main()
{
  var x, y: int;
  var v1, v2, v3: int;

  x := 0; 
  y := 0;

  while (y >= 0)
  invariant b0(x,y, v1, v2, v3);
  {
    y := y + x;
    havoc v1;
    havoc v2;
    havoc v3;

  }
  assert false;
}

