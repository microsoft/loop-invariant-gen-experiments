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
// Updated invariants
invariant x >= 0;
invariant x <= 2 * y + 2;
invariant y >= 0;
invariant y <= 2 * x + 2;
invariant (y != 0) ==> (x != 4);
invariant (y == 0) ==> (x % 2 == 0);
{
    havoc nondet;
x := x + 2;
y := y + 2;
}
if(y == 0) {
assert(x != 4);
}
}