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
invariant x <= 2 + 2 * (y div 2);
{
x := x + 2;
y := y + 2;
}
if(x == 4) {
assert(y != 0);
}
}