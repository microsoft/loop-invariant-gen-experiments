function {:existential true} b0(x:int, n:int): bool;

var x, n: int;

procedure main()
modifies x;
{
  x := 0;
  assume n >= 0;
  while (x < n)
  invariant b0(x, n);
  {
    x := x + 1;
  }
  assert x == n;
}

