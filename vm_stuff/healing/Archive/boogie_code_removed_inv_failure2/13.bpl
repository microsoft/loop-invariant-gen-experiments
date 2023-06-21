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
// fixed invariants
invariant x mod 2 == y mod 2;
invariant x >= 0;
invariant y >= 0; // Fix: make y >= 0 unconditionally hold
invariant y <= 2 || (y >= 4 && y <= 6);
invariant (x + y >= 2) || (x == 0 && y == 0);
invariant (x == 4) ==> (y != 0);
{
x := x + 2;
y := y + 2;
}
if(x == 4) {
assert(y != 0);
}
}