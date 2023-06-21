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
invariant 0 <= x <= n;
invariant 0 <= m <= x;
invariant 0 <= x <= n;
invariant 0 <= m <= x;
invariant 0 <= x <= n;
invariant 0 <= m <= x;
{
havoc nondet;
if(nondet) {
m := x;
}
x := x + 1;
}
if(n > 0) {
assert(m >= 0);
}
}