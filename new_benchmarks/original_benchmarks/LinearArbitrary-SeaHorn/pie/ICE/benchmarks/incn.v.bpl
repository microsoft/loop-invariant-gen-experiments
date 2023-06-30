function {:existential true} b0(x:int, N: int, v1: int, v2: int, v3: int): bool;


procedure main()
{
  var x, N: int;
  var v1, v2, v3: int;

  x := 0;
  while (x < N)
  invariant b0(x, N, v1, v2, v3);
  {
    x := x + 1;
    havoc v1;
    havoc v2;
    havoc v3;
  }
  assert N < 0 || x == N;
}

