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
invariant x >= 0; // Invariant 1: 0 <= x <= 20
invariant y >= 0; // Modified Invariant 2: y >= 0
invariant (x == 20) ==> (y >= 10); // Additional Invariant: if x == 20, then y >= 10
{
x := x + 10;
y := y + 10;
}
if(x == 20) {
assert(y != 0);
}
}