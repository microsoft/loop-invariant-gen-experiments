function {:existential true} b0(x:int, N: int): bool;


procedure main()
{
  var x, N: int;
  x := 0;
  while (x < N)
  invariant b0(x, N);
  {
    x := x + 1;
  }
  assert N < 0 || x == N;
}

