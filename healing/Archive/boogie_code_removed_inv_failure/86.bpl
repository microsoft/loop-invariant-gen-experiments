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
invariant x = -50 + y * (y - 1) div 2;
invariant y >= 0;
invariant x + y * (y - 1) div 2 = -50;
invariant x < 0;
invariant y >= 0;
y := 1; // Initializing y to 1 to satisfy the loop invariant
invariant x + y = -49;
invariant x < 0;
invariant y >= 1;
{
x := x + y;
y := y + 1;
}
assert(y > 0);
}