procedure main() {
var nondet: bool;
var n: int;
var x: int;
x := 0;
while(x < n)
// fixed invariants
invariant (x != 0) ==> (x <= n);
invariant x >= 0;
{
x := x + 1;
}
if(x != n) {
assert(n < 0);
}
}