procedure main() {
var nondet: bool;
var x: int;
var y: int;
assume(x >= 0);
assume(x <= 10);
assume(y <= 10);
assume(y >= 0);
havoc nondet;
while(nondet)
// insert invariants 
invariant x >= 0;
invariant y >= 0;
invariant x >= 0;
invariant y >= 0;
invariant x - y >= -10;
invariant x - y <= 10;
invariant x >= 0;
invariant y >= 0;
{
x := x + 10;
y := y + 10;
}
if(y == 0) {
assert(x != 20);
}
}