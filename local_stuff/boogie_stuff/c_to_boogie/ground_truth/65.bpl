procedure main() {
var nondet: bool;
var x: int;
var y: int;
x := 1;
while(x <= 100)
// insert invariants 
invariant x >= 1 && x <= 101;
invariant x == 1 || y >= 0;
invariant x == 1 || 100 - x <= y;
{
y := 100 - x;
x := x + 1;
}
assert(y >= 0);
}