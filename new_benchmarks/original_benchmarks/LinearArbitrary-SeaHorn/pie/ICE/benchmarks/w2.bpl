function {:existential true} b0(x:int, n:int): bool;

var x, n: int;

procedure main()
modifies x;
{
  x := 0;
  assume n > 0;
  while (true)
  invariant b0(x, n);
  {
    if(*)
    {
      x := x + 1;
      if(x >= n)
      {
        break;
      }
    }
  }
  assert x == n;
}

