procedure main() {
var nondet: bool;
var x: int;
var y: int;
x := 1;
y := 0;
while(y < 100000)
// insert invariants 
invariant x == 1 + y * (y - 1) div 2;
invariant x == 1 + y * (y - 1) div 2;
invariant x == 1 + y * (y - 1) div 2;
{
x := x + y;
y := y + 1;
}
assert(x >= y);
}