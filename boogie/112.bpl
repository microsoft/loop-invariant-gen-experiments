 procedure main()
{
var i: int;
var n: int;
var sn: int;
var v1: int;
var v2: int;
var v3: int;
// pre-conditions
sn := 0;
i := 1;
// loop body
while (i <= n)
invariant sn == i-1;
{
i := i + 1;
sn := sn + 1;
}
// post-condition
if(sn != n) {
assert(sn == 0);
}
}