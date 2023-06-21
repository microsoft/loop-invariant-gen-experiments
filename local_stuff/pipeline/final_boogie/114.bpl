procedure main() {
var nondet: bool;
var sn: int;
var x: int;
sn := 0;
x := 0;
havoc nondet;
while(nondet)
// insert invariants 
invariant sn == x;
invariant sn == x;
invariant sn == x;
{
x := x + 1;
sn := sn + 1;
}
if(sn != x) {
assert(sn == -1);
}
}