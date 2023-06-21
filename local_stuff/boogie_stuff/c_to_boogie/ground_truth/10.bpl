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
invariant x - y <= 2 && y - x <= 2;
{
x := x + 2;
y := y + 2;
}
if(y == 0) {
assert(x != 4);
}
}