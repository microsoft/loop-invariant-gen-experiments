function {:existential true} b0(x:int, y:int): bool;

procedure main()
{
  var x, y: int;
  var a: [int]int;

  x := 1;

  while (x <= 10)
  invariant b0(x,y);
  {
    y := 10 - x;
    if (y < 0 || y >= 10)
    {
      assert false;
    }
    a[y] := -1;
    x := x + 1;
  }
}

