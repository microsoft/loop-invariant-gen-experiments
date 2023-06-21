procedure main()
{
  var x: int;
  var m: int;
  var n: int;
  var nondet: bool;
  // variable initialization
  x := 0;
  m := 0;
  // loop body
  havoc nondet;
  while (x < n)
  invariant 0 <= x && x <= n;
  invariant 0 <= m && m <= x;
  {
    havoc nondet;
    if (nondet) {
      m := x;
    }
    x := x + 1;
  }
  // post-condition
  if (n > 0) {
    //assert(m < n);
    assert(m >= 0);
  }
}