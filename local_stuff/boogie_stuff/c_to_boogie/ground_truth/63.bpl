procedure main() {
var nondet: bool;
var x: int;
var y: int;
x := 1;
while(x <= 10)
// insert invariants 
invariant x >= 1 && x <= 11;
invariant (x == 1) || (0 <= y && y <= 9);
{
y := 10 - x;
x := x + 1;
}
assert(y >= 0);
}