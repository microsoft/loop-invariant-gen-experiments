 procedure main()
{
var sn: int;
var v1: int;
var v2: int;
var v3: int;
var x: int;
var nondet: bool;
// pre-conditions
sn := 0;
x := 0;
// loop body
havoc nondet;
while (nondet)
invariant sn == x;
{
havoc nondet;
x := x + 1;
sn := sn + 1;
}
// post-condition
if(sn != x) {
assert(sn == -1);
}
}