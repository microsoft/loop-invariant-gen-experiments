procedure main() {
var nondet: bool;
var n: int;
var x: int;
x := n;
while(x > 1)
// insert invariants 
{
x := x - 1;
}
if(n >= 0) {
assert(x == 1);
}
}