function {:existential true} b0(x:int, y:int, lock:int, v1: int, v2: int, v3: int): bool;

var y: int;

procedure main()
modifies y;
{
  var x, lock: int;
  var v1, v2, v3: int;

  lock := 0;

  lock := 1;
  x := y;
  if (*)
  {
    lock := 0;
    y := y + 1;
  }
  havoc v1;
  havoc v2;
  havoc v3;

  while (x != y)
  invariant b0(x, y, lock, v1, v2, v3);
  {
    lock := 1;
    x := y;
    if (*)
    {
      lock := 0;
      y := y + 1;
    }
    havoc v1;
    havoc v2;
    havoc v3;

  }
  assert lock == 1;
}

