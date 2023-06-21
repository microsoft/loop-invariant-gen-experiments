procedure main() {
var nondet: bool;
var x: int;
var y: int;
x := -5000;
while(x < 0)
// loop invariants
invariant x <= -5000 || (x > -5000 && y > 0);
{
x := x + y;
y := y + 1;
}
assert(y > 0);
}