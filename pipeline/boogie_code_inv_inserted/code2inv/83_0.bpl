procedure main() {
var nondet: bool;
var x: int;
var y: int;
x := -5000;
while(x < 0)
// insert invariants 
// loop invariants
invariant x + y * (y - 1) div 2 == -5000 + C;
{
x := x + y;
y := y + 1;
}
assert(y > 0);
}