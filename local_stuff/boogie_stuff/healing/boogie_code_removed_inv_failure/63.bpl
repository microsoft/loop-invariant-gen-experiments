procedure main() {
var nondet: bool;
var x: int;
var y: int;
x := 1;
while(x <= 10)
// insert invariants 
invariant x >= 1;
invariant x <= 11;
invariant y == 10 - x + 1;
invariant x <= 11;
invariant y >= -1;
invariant y == 10 - x + 1;
invariant x >= 1;
invariant x <= 11;
{
y := 10 - x;
x := x + 1;
}
assert(y >= 0);
}