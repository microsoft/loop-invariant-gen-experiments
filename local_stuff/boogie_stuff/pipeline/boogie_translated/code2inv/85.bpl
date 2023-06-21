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
{
x := x + y;
y := y + 1;
}
assert(y > 0);
}