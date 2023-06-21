procedure main() {
var nondet: bool;
var x: int;
var y: int;
var z1: int;
var z2: int;
var z3: int;
x := -50;
while(x < 0)
// fixed invariants
invariant x >= -50;
invariant y >= 0;
invariant (x != -50) ==> (y > 0);
invariant (x == -50) ==> (y == 0);
invariant (x != -50) ==> (y * (y - 1) div 2 >= -x);
invariant (x < 0) ==> (x + (y * (y + 1) div 2) == -50);
invariant (x == 0) ==> (y * (y + 1) div 2 == 50);
{
x := x + y;
y := y + 1;
}
assert(y > 0);
}