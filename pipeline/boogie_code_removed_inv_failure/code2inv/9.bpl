procedure main() {
var nondet: bool;
var x: int;
var y: int;
assume(x >= 0);
assume(x <= 2);
assume(y <= 2);
assume(y >= 0);
havoc nondet;
while(nondet)
// insert invariants 
invariant x >= 0;
invariant x <= 2 + 2 * (y + 1);
invariant y >= 0;
invariant y <= 2 + 2 * (x + 1);
invariant x >= 0;
invariant x <= 2 + 2 * (y + 1);
invariant y >= 0;
invariant y <= 2 + 2 * (x + 1);
invariant D == x - y;
invariant x >= 0;
invariant x <= 2 + 2 * (y + 1);
invariant y >= 0;
invariant y <= 2 + 2 * (x + 1);
invariant x_initial + y_initial = x + y;
{
x := x + 2;
y := y + 2;
}
if(x == 4) {
assert(y != 0);
}
}