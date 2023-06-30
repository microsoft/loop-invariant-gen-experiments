function {:existential true} b0(x:int, N: int, v1: int, v2: int, v3: int): bool;


procedure main()
{
  var x, m: int;
  var N: int;
  var v1, v2, v3: int;

  x := N;
  while (x > 0)
  invariant b0(x, N, v1, v2, v3);
  //invariant (x <= -1 && N <= -1) || x > -1; 
  {
    x := x - 1;
    havoc v1;
    havoc v2;
    havoc v3;
  }
  assert N < 0 || x == 0;
}

