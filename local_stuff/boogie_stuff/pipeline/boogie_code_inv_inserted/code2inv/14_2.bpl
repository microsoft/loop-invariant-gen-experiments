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
// insert invariants 
invariant x mod 2 == y mod 2;
invariant x >= 0;
invariant x <= 4;
invariant y >= 0;
invariant y <= 4;
{
x := x + 2;
y := y + 2;
}
if(y == 0) {
assert(x != 4);
}
}