procedure main() {
var nondet: bool;
var x: int;
var y: int;
x := 1;
while(x < y)
// insert invariants 
{
x := x + x;
}
assert(x >= 1);
}