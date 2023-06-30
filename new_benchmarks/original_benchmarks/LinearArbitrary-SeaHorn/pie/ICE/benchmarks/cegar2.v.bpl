function {:existential true} b0(x:int, m:int, N:int, v1: int, v2: int, v3: int): bool;

var N: int;


procedure {:entrypoint} main()
{
  var x, m: int;
  var v1, v2, v3: int;
  x := 0;
  m := 0;

  while (x < N)
  invariant b0(x, m, N, v1, v2, v3);
  {
    if (*)
    {
      m := x;
    }
    x := x + 1;
    havoc v1;
    havoc v2;
    havoc v3;
  }
  //assert (N <= 0 || (0 <= m && m < N));
  if (N > 0)
  {
      assert (0 <= m && m < N);
  }
}

