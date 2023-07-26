function {:existential true} b0(x:int, m:int, N:int, v1: int, v2: int, v3: int, v4: int, v5: int, v6: int, v7: int, v8: int, v9: int): bool;

var N: int;


procedure {:entrypoint} main()
{
  var x, m: int;
  var v1, v2, v3, v4, v5, v6, v7, v8, v9: int;
  x := 0;
  m := 0;

  while (x < N)
  invariant b0(x, m, N, v1, v2, v3, v4, v5, v6, v7, v8, v9);
  {
    if (*)
    {
      m := x;
    }
    x := x + 1;
    havoc v1;
    havoc v2;
    havoc v3;
    havoc v4;
    havoc v5;
    havoc v6;
    havoc v7;
    havoc v8;
    havoc v9;
  }
  //assert (N <= 0 || (0 <= m && m < N));
  if (N > 0)
  {
      assert (0 <= m && m < N);
  }
}

