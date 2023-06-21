procedure main()
{
  var c: int;
  var nondet: bool;
  var nondet_if: bool;
  // pre-conditions
  c := 0;
  // loop body
  havoc nondet;
  while (nondet)
  invariant 0 <= c && c <= 40;
  {
    havoc nondet;
    havoc nondet_if;
    if (nondet_if) {
      if (c != 40) {
        c := c + 1;
      }
    } else {
      if (c == 40) {
        c := 1;
      }
    }
  }
  // post-condition
  if (c != 40) {
    assert(c <= 40);
  }
}