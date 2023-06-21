procedure main() {
var nondet: bool;
var x: int;
var y: int;
x := 1;
while(x <= 10)
// updated invariants
invariant x >= 1;
invariant x <= 11;
invariant x > 1 ==> y == 10 - x + 1;
{
y := 10 - x;
x := x + 1;
}
assert(y >= 0);
}