procedure main() {
var nondet: bool;
var x: int;
var y: int;
x := 1;
while(x <= 10)
// insert invariants 
{
y := 10 - x;
x := x + 1;
}
assert(y < 10);
}