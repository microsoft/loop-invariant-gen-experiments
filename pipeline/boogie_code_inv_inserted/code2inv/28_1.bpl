procedure main() {
var nondet: bool;
var n: int;
var x: int;
x := n;
while(x > 0)
// insert invariants 
invariant x == n - iteration;
{
x := x - 1;
}
if(x != 0) {
assert(n < 0);
}
}