procedure main() {
var nondet: bool;
var x: int;
x := 10000;
while(x > 0)
// insert invariants 
{
x := x - 1;
}
assert(x == 0);
}