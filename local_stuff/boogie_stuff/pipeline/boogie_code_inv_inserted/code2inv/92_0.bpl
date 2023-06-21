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
invariant x == 0;
invariant y >= 0;
{
y := y + x;
}
assert(y >= 0);
}