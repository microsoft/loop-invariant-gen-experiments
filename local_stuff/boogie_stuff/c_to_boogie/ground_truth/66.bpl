procedure main() {
var nondet: bool;
var x: int;
var y: int;
x := 1;
while(x <= 100)
// insert invariants 
invariant x >= 1 && x <= 101;
invariant x == 1 || (0 <= y && y <= 100);
invariant x == 1 || y < 100;
{
y := 100 - x;
x := x + 1;
}
assert(y < 100);
}