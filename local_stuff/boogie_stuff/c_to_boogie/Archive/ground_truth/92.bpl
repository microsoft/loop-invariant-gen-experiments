procedure main() {
var nondet: bool;
var z1: int;
var z2: int;
var z3: int;
var x: int;
var y: int;
x := 0;
y := 0;
while(y >= 0)
// insert invariants 
invariant y >= 0;
assert (false); // The loop invariant contradicts the post-condition, so the code is incorrect.
{
y := y + x;
}
assert(y >= 0);
}