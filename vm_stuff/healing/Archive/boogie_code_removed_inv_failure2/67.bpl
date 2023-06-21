procedure main() {
var nondet: bool;
var n: int;
var y: int;
var x: int;
x := 1;
while(x <= n)
// fixed invariants
invariant 1 <= x && x <= n+1;
invariant x == 1 || (x > 1 && y == n - (x - 2));
invariant x == 1 || y + x == n + 1;
invariant x > n || y == n - x + 1;
invariant n <= 0 || y >= 0; // Added invariant to ensure y is non-negative when n > 0
{
y := n - x;
x := x + 1;
}
if(n > 0) {
assert(y >= 0);
}
}