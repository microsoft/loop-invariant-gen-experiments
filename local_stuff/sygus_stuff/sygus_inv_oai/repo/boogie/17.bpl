procedure main()
{
  var x: int;
  var m: int;
  var n: int;
  var nondet: bool;
  // Initialization
  x := 1;
  m := 1;
  // loop body
  havoc nondet;
  while (x < n)
  invariant 1 <= m && m <= x && x <= n;
  {
    havoc nondet;
    if (nondet) {
      m := x;
    }
    x := x + 1;
  }
  // post-condition
  if(n > 1) {
    assert(m < n);
    //assert(m >= 1);
  }
}