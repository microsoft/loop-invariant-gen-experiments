procedure main() {
var nondet: bool;
var n: int;
var x: int;
x := 0;
assume(n >= 0);
while(x < n)
// insert invariants 
invariant x <= n;
invariant x <= n;
invariant x <= n;
{
x := x + 1;
}
assert(x == n);
}