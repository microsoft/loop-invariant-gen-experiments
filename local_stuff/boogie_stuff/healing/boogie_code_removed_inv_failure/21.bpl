procedure main() {
var nondet: bool;
var z1: int;
var z2: int;
var z3: int;
var x: int;
var m: int;
var n: int;
x := 1;
m := 1;
while(x < n)
// insert invariants 
invariant 1 <= m <= x;
invariant 1 <= m <= x;
invariant (forall k: int :: (1 <= k < x && unknown) ==> (m >= k));
invariant 1 <= m <= x;
{
havoc nondet;
if(nondet) {
m := x;
}
x := x + 1;
}
if(n > 1) {
assert(m < n);
}
}