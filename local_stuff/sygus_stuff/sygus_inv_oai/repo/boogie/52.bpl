procedure main()
{
  var c: int;
  var nondet: bool;
  var nondet2: bool;
  // pre-conditions
  assume(c = 0);
  // loop body
  havoc nondet;
  while (nondet)
  invariant 0 <= c && c <= 4;
  {
    havoc nondet;
    havoc nondet2;
    if (nondet2) {
      if (c != 4) {
        c := c + 1;
      }
    } else {
      if (c == 4) {
        c := 1;
      }
    }
  }
  // post-condition
  if (c < 0 || c > 4) {
    assert(c == 4);
  }
}