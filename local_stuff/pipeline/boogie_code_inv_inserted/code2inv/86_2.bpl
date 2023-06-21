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