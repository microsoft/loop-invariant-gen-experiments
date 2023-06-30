function {:existential true} b0(x:int, y:int, lock:int): bool;

var y: int;

procedure main()
modifies y;
{
  var x, lock: int;
  lock := 0;

  lock := 1;
  x := y;
  if (*)
  {
    lock := 0;
    y := y + 1;
  }

  while (x != y)
  invariant b0(x, y, lock);
  {
    lock := 1;
    x := y;
    if (*)
    {
      lock := 0;
      y := y + 1;
    }
  }
  assert lock == 1;
}

