procedure main() {
var nondet: bool;
var x: int;
var y: int;
x := 1;
while(x <= 100)
// insert invariants 
{
y := 100 - x;
x := x + 1;
}
assert(y < 100);
}