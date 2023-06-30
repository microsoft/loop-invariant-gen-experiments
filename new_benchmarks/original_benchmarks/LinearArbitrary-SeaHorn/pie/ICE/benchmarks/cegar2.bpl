function {:existential true} b0(x:int, m:int, N:int): bool;

var N: int;


procedure {:entrypoint} main()
{
  var x, m: int;
  x := 0;
  m := 0;

  while (x < N)
  invariant b0(x, m, N);
  {
    if (*)
    {
      m := x;
    }
    x := x + 1;
  }
  //assert (N <= 0 || (0 <= m && m < N));
  if (N > 0)
  {
      assert (0 <= m && m < N);
  }
}

