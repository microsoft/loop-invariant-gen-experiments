procedure main() {
var nondet: bool;
var n: int;
var x: int;
x := n;
while(x > 0)
// insert invariants 
invariant x >= 0;
invariant x <= n;
{
x := x - 1;
}
if(x != 0) {
assert(n < 0);
}
}