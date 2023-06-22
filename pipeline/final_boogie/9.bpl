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
invariant x >= 0;
invariant y >= 0;
invariant x <= 2 + 2 * y;
invariant y <= 2 + 2 * x;
{
x := x + 2;
y := y + 2;
}
if(x == 4) {
assert(y != 0);
}
}