procedure main() {
var nondet: bool;
var x: int;
var y: int;
x := -50;
while(x < 0)
// insert invariants 
{
x := x + y;
y := y + 1;
}
assert(y > 0);
}