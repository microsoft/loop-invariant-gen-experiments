procedure main() {
var nondet: bool;
var n: int;
var x: int;
x := 0;
while(x < n)
// insert invariants 
invariant x >= 0;
invariant x <= n;
{
x := x + 1;
}
if(x != n) {
assert(n < 0);
}
}