procedure main() {
var nondet: bool;
var n: int;
var y: int;
var x: int;
x := 1;
while(x <= n)
// insert invariants 
invariant x >= 1;
invariant y == n - x + 1;
{
y := n - x;
x := x + 1;
}
if(n > 0) {
assert(y <= n);
}
}