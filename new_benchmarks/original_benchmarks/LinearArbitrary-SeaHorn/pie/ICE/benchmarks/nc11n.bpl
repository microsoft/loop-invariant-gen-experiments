function {:existential true} b0(i:int, len:int, N: int): bool;

procedure main()
{
  var len, i: int;
  var N: int;
  var a: [int]int;
  len := 0;

  assume N > 0;
  while ( * )
  invariant b0(i,len,N);
  {
    if (len == N)
    {
      len := 0;
    }
    if (len < 0 || len >= N + 1)
    {
      assert false;
    }
    len := len + 1;
  }
}

