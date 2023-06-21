procedure main() {
var nondet: bool;
var x: int;
var y: int;
x := 0;
y := 0;
while(y >= 0)
// insert invariants 
invariant x == 0;
invariant y >= 0;
invariant x == 0;
invariant y >= 0;
invariant x == 0;
invariant y >= 0;
{
y := y + x;
}
assert(y >= 0);
}