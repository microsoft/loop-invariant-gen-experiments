procedure main() {
var nondet: bool;
var n: int;
var v1: int;
var v2: int;
var v3: int;
var x: int;
var y: int;
x := 1;
while(x <= n)
// insert invariants 
invariant x >= 1;
invariant (x == 1 || y < n);
{
y := n - x;
x := x + 1;
}
if(n > 0) {
assert(y < n);
}
}