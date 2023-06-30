function {:existential true} b0(y:int, z:int, c:int, v1: int, v2: int, v3: int): bool;

var x: [int]int;
var y: int;

procedure main()
modifies x, y;
{
  var c, z: int;
  var v1, v2, v3: int;

  c := 0;

  if(127 < y)
  {
    goto exit;
  }
  if (y < 0)
  {
    goto exit;
  }
  z := y * 36;
  while (c < 36)
  invariant b0(y,z,c, v1, v2, v3);
  // 0 <= y inferred automatically since y is not modified inside the loop !
  {
    if (z < 0 || z >= 4608)
    {
      assert false;
    }
    x[z] := 0;
    z := z + 1;
    c := c + 1;
    havoc v1;
    havoc v2;
    havoc v3;
  }
  
exit:
}

