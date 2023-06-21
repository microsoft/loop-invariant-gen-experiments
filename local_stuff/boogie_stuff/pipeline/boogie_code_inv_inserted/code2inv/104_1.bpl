procedure main() {
var nondet: bool;
var n: int;
var v1: int;
var v2: int;
var v3: int;
var x: int;
x := 0;
while(x < n)
// insert invariants 
invariant x <= n;
{
x := x + 1;
}
if(x != n) {
assert(n < 0);
}
}