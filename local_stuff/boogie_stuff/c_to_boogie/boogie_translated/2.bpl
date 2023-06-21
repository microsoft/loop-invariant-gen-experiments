procedure main() {
var nondet: bool;
var x: int;
var y: int;
x := 1;
y := 0;
while(y < 1000)
// insert invariants 
invariant y >= 0;
invariant x >= y;
{
x := x + y;
y := y + 1;
}
assert(x >= y);
}