function {:existential true} b0(x:int, n:int, v1: int, v2: int, v3: int): bool;

var x, n: int;

procedure main()
modifies x;
{
  var v1, v2, v3: int;

  x := 0;
  assume n > 0;
  while (true)
  invariant b0(x, n, v1, v2, v3);
  {
    if(*)
    {
      x := x + 1;
      if(x >= n)
      {
        break;
      }
    }
    havoc v1;
    havoc v2;
    havoc v3;
  }
  assert x == n;
}

