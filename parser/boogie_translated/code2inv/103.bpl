procedure main() {
var nondet: bool;
var x: int;
x := 0;
while(x < 100)
// insert invariants 
{
x := x + 1;
}
assert(x == 100);
}