procedure main()
{
  var x: int;
  var y: int;
  var nondet: bool;
  // pre-conditions
  assume(0 <= x);
  assume(x <= 10);
  assume(y <= 10);
  assume(y >= 0);
  // loop body
  havoc nondet;
  while (nondet)
  invariant x-y <= 10 && y - x <= 10;
  {
    havoc nondet;
    x := x + 10;
    y := y + 10;
  }
  // post-condition
  if(y==0) {
    assert(x != 20);
  }
}