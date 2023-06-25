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
invariant x % 2 == y % 2; // Invariant 1: x and y have the same parity
invariant x >= 0; // Invariant 2: 0 <= x <= 20
invariant x <= 20;
invariant y >= 0; // Invariant 3: 0 <= y <= 20
invariant y <= 20;
{
x := x + 10;
y := y + 10;
}
if(x == 20) {
assert(y != 0);
}
}