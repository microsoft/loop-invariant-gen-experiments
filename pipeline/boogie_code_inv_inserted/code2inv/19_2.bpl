procedure main() {
var nondet: bool;
var z1: int;
var z2: int;
var z3: int;
var x: int;
var m: int;
var n: int;
x := 0;
m := 0;
while(x < n)
// insert invariants 
invariant 0 <= x;
invariant 0 <= m;
invariant m <= x;
invariant x <= n;
// assert(m >= 0); // This assertion is always true due to the loop invariant
{
havoc nondet;
if(nondet) {
m := x;
}
x := x + 1;
}
if(n > 0) {
assert(m < n);
}
}