function {:existential true} b0(i:int, len:int, N: int, v1: int, v2: int, v3: int): bool;

procedure main()
{
  var len, i: int;
  var N: int;
  var v1, v2, v3: int;

  var a: [int]int;
  len := 0;

  assume N > 0;
  while ( * )
  invariant b0(i,len,N,v1,v2,v3);
  {
    if (len == N)
    {
      len := 0;
    }
    if (len < 0 || len > N)
    {
      assert false;
    }
    len := len + 1;
    havoc v1;
    havoc v2;
    havoc v3;
  }
}

