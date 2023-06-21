procedure main() {
var nondet: bool;
var n: int;
var v1: int;
var v2: int;
var v3: int;
var x: int;
x := n;
while(x > 0)
// insert invariants
invariant x <= n;
invariant n - x >= 0;
invariant n >= 0 ==> x >= 0; // Updated invariant with an implies clause
{
x := x - 1;
}
if(x != 0) {
assert(n < 0);
}
}