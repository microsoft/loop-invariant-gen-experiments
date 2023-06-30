function {:existential true} b0(x:int, y:int, v1: int, v2: int, v3: int): bool;

procedure main()
{
  var x, y: int;
  var a: [int]int;
  var N: int;
  var v1, v2, v3: int;

  x := 1;

  while (x <= N)
  invariant b0(x,y, v1, v2, v3);
  {
    y := N - x;
    if (y < 0 || y >= N)
    {
      assert false;
    }
    a[y] := -1;
    x := x + 1;
    havoc v1;
    havoc v2;
    havoc v3;
  }
}

