procedure main() {
var nondet: bool;
var x: int;
var y: int;
var z1: int;
var z2: int;
var z3: int;
x := 1;
while(x < y)
// insert invariants 
invariant x >= 1;
invariant x == 2 ** (old(x) - 1);
{
x := x + x;
}
assert(x >= 1);
}