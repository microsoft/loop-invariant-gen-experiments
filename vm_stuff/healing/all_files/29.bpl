procedure main() {
var nondet: bool;
var n: int;
var x: int;
x := n;
while(x > 0)
// insert invariants
invariant n - x >= 0;
invariant (!(x > 0)) ==> (n >= 0 ==> x == 0);
{
x := x - 1;
}
if(n >= 0) {
assert(x == 0);
}
}