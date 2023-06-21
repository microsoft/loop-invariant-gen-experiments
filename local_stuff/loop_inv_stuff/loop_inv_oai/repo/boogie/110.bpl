procedure main()
{
  var i: int;
  var n: int;
  var sn: int;
  // pre-conditions
  sn := 0;
  i := 1;
  // loop body
  while (i <= n)
  invariant 0 <= i && i <= n + 1;
  invariant sn == i - 1;
  {
    i := i + 1;
    sn := sn + 1;
  }
  // post-condition
  if (sn != n) {
    assert(sn == 0);
  }
}