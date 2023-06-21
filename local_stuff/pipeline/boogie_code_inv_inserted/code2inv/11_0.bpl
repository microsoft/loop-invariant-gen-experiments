procedure main() {
var nondet: bool;
var x: int;
var y: int;
var z1: int;
var z2: int;
var z3: int;
assume(x >= 0);
assume(x <= 10);
assume(y <= 10);
assume(y >= 0);
havoc nondet;
while(nondet)
// insert invariants 
invariant x >= 0;
invariant y >= 0;
invariant x mod 10 == 0;
invariant y mod 10 == 0;
{
x := x + 10;
y := y + 10;
}
if(x == 20) {
assert(y != 0);
}
}