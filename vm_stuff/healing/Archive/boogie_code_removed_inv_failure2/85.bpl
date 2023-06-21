procedure main() {
var nondet: bool;
var x: int;
var y: int;
var z1: int;
var z2: int;
var z3: int;
x := -15000;
while(x < 0)
// insert invariants
invariant x <= 0;
invariant x < 0 ==> y >= 0;
invariant x + 15000 <= y * (y - 1) div 2;
invariant (y == 0) ==> (x == -15000);
invariant x + y * (y + 1) div 2 == -15000;
{
x := x + y;
y := y + 1;
}
assert(y > 0);
}