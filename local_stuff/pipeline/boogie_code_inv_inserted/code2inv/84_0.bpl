procedure main() {
var nondet: bool;
var x: int;
var y: int;
x := -50;
while(x < 0)
// insert invariants 
invariant x < 0;
invariant y >= 0;
{
x := x + y;
y := y + 1;
}
assert(y > 0);
}