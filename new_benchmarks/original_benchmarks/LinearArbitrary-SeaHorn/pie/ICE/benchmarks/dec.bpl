function {:existential true} b0(x:int, m: int): bool;


procedure main()
{
  var x, m: int;
  x := 100;
  while (x > 0)
  invariant b0(x, m);
  {
    havoc m;
    x := x - 1;
  }
  assert x == 0;
}

