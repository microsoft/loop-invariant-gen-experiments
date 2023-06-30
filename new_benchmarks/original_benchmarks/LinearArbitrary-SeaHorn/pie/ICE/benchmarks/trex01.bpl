function {:existential true} b0(x:int,y:int,k:int,z:int,c:int): bool;
//function {:existential true} b1(x:int,y:int,k:int,z:int,c:int): bool;

var d: int;

procedure main()
{

  var x, y, k, z, c: int;
  z := 1;

  while ( z < k )
  invariant b0(x,y,k,z,c);
  {
    z := 2 * z;
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

