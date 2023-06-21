procedure main() {
var nondet: bool;
var n: int;
var x: int;
x := n;
while(x > 1)
// insert invariants 
invariant x == n - i;
invariant i >= 0;
invariant x == n - i;
invariant i >= 0;
invariant x <= n;
{
x := x - 1;
}
if(x != 1) {
assert(n < 0);
}
}