procedure main() {
var nondet: bool;
var x: int;
var y: int;
x := -50;
while(x < 0)
// modified invariants
invariant x >= -50;
invariant y >= 0;
invariant x < 0 ==> y == 0 || x + y * (y - 1) / 2 == -50;
{
x := x + y;
y := y + 1;
}
assert(y > 0);
}