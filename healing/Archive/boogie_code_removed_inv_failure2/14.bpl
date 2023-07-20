procedure main() {
var nondet: bool;
var x: int;
var y: int;
var z1: int;
var z2: int;
var z3: int;
assume(x >= 0);
assume(x <= 2);
assume(y <= 2);
assume(y >= 0);
havoc nondet;
while(nondet)
// updated invariants
invariant x >= 0;
invariant y >= 0;
invariant (!nondet ==> x <= 4); // conditionally hold after loop entry
invariant (!nondet ==> y <= 4); // conditionally hold after loop entry
invariant (x % 2 == y % 2); // strengthen x mod 2 == y mod 2
invariant !(x == 4 && y == 4); // x and y cannot both be 4
{
x := x + 2;
y := y + 2;
}
if(y == 0) {
assert(x != 4);
}
}