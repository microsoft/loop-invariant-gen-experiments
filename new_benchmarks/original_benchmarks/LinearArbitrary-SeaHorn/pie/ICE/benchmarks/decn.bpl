function {:existential true} b0(x:int, N: int): bool;


procedure main()
{
  var x, m: int;
  var N: int;
  x := N;
  while (x > 0)
  invariant b0(x, N);
  {
    x := x - 1;
  }
  assert N < 0 || x == 0;
}

