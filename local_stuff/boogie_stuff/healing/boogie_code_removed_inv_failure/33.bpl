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
invariant x == n - k;
invariant k >= 0;
invariant x == n - iteration_count;
invariant iteration_count >= 0;
{
x := x - 1;
}
if(x != 0) {
assert(n < 0);
}
}