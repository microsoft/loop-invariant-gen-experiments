procedure main()
{
  var i: int;
  var sn: int;
  // pre-conditions
  sn := 0;
  i := 1;
  // loop body
  while (i <= 8)
  invariant 0 <= sn && sn <= 8 && sn == i - 1;
  {
    i := i + 1;
    sn := sn + 1;
  }
  // post-condition
  if (sn != 8) {
    assert(sn == 0);
  }
}