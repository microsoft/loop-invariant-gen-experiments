procedure main() {
var nondet: bool;
var n: int;
var v1: int;
var v2: int;
var v3: int;
var x: int;
x := n;
while(x > 1)
// insert invariants 
invariant n - x >= 0;
invariant x >= 1;
invariant x == n - (n - x);
invariant x >= 1;
invariant x >= 1;
invariant x <= n;
{
x := x - 1;
}
if(n >= 0) {
assert(x == 1);
}
}