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
invariant x <= 10 + 10 * (y div 10);
{
x := x + 10;
y := y + 10;
}
if(x == 20) {
assert(y != 0);
}
}