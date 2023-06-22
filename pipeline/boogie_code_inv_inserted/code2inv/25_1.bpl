procedure main() {
var nondet: bool;
var x: int;
x := 10000;
while(x > 0)
// insert invariants 
invariant x >= 0;
invariant x == remaining_iterations;
{
x := x - 1;
}
assert(x == 0);
}