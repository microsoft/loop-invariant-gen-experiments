function {:existential true} b0(x:int, y:int): bool;

procedure main()
{
  var x, y: int;
  x := 0; 
  y := 0;

  while (y >= 0)
  invariant b0(x,y);
  {
    y := y + x;
  }
  assert false;
}

