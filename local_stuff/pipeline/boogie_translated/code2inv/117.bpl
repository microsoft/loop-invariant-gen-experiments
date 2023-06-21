procedure main() {
var nondet: bool;
var sn: int;
var v1: int;
var v2: int;
var v3: int;
var x: int;
sn := 0;
x := 0;
havoc nondet;
while(nondet)
// insert invariants 
{
x := x + 1;
sn := sn + 1;
}
if(sn != -1) {
assert(sn == x);
}
}