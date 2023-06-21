procedure main() {
var nondet: bool;
var x: int;
var y: int;
var z1: int;
var z2: int;
var z3: int;
x := -50;
while(x < 0)
// insert invariants 
invariant x + y * (y - 1) div 2 == -50;
invariant y >= 0;
{
x := x + y;
y := y + 1;
}
assert(y > 0);
}