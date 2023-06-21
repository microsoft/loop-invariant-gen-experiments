procedure main() {
var nondet: bool;
var x: int;
x := 100;
while(x > 0)
// insert invariants 
invariant x >= 0;
invariant x <= 100;
invariant x == 100 - iterations;
{
x := x - 1;
}
assert(x == 0);
}