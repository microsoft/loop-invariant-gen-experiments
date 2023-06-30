function {:existential true} b0(i:int, len:int): bool;

procedure main()
{
  var len, i: int;
  var a: [int]int;
  len := 0;

  while ( * )
  invariant b0(i,len);
  {
    if (len == 4)
    {
      len := 0;
    }
    if (len < 0 || len >= 5)
    {
      assert false;
    }
    len := len + 1;
  }
}

