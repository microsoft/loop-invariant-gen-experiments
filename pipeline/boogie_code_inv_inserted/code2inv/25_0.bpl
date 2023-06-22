procedure main() {
var nondet: bool;
var x: int;
x := 10000;
while(x > 0)
// insert invariants 
invariant x >= 0;
invariant initial_x - x == num_iterations;
{
x := x - 1;
}
assert(x == 0);
}