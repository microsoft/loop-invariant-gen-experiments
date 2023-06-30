function {:existential true} b0(i:int, y:int, len:int): bool;

var x: int;
var y: int;

procedure main()
modifies x, y;
{
  var a: [int]int;

  var i, len: int;
  if (x < 0 || y < 0 || y > x) 
  {
    goto exit;
  }

  len := x;
  i := 0;
  while (i < y)
  invariant b0(i, y, len);
  // invariant y <= len is automatically inferred because y, len are not modified inside the loop !
  {
    if(i < 0 || i >= len)
    {
      assert (false);
    }
    a[i] := 0;
    i := i + 1;
  }
exit:
}

