function {:existential true} b0(x:int,y:int,k:int,z:int,c:int, v1:int, v2:int, v3:int): bool;
//function {:existential true} b1(x:int,y:int,k:int,z:int,c:int): bool;

var d: int;

procedure main()
{

  var x, y, k, z, c: int;
  var v1, v2, v3: int;
  z := 1;

  while ( z < k )
  invariant b0(x,y,k,z,c,v1,v2,v3);
  {
    z := 2 * z;
    havoc v1;
    havoc v2;
    havoc v3;
  }
  assert z >= 1;

  while (x > 0 && y > 0)
  //invariant b1(x,y,k,z,c);
  {
    havoc c;
    if (c == 0)
    {
      y := y - d;
    } 
    else
    {
      x := x - d;
      havoc y;
      z := z - 1;
    }
  }
}

