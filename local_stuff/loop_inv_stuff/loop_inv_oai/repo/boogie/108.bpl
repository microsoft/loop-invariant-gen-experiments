procedure main()
{
  var a: int;
  var c: int;
  var m: int;
  var j: int;
  var k: int;

  // pre-conditions
  assume(a <= m);
  j := 0;
  k := 0;

  // loop body
  while (k < c)
  invariant a <= m;
  {
    if(m < a) {
      m := a;
    }
    k := k + 1;
  }

  // post-condition
  assert(a <= m);
}