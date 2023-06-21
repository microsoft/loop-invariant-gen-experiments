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
invariant x >= 0;
invariant x <= n;
invariant x >= 0;
invariant x <= n;
invariant x >= 0;
invariant x <= n;
{
x := x + 1;
}
if(n >= 0) {
assert(x == n);
}
}