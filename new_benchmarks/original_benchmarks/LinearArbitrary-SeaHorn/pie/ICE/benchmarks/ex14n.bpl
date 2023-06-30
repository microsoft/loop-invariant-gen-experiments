function {:existential true} b0(x:int, y:int): bool;

procedure main()
{
  var x, y: int;
  var a: [int]int;
  var N: int;

  x := 1;

  while (x <= N)
  invariant b0(x,y);
  {
    y := N - x;
    if (y < 0 || y >= N)
    {
      assert false;
    }
    a[y] := -1;
    x := x + 1;
  }
}

