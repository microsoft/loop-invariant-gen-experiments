procedure main() {
var nondet: bool;
var x: int;
var y: int;
x := 1;
while(x <= 100)
// insert invariants
invariant x >= 1;
invariant x <= 101;
invariant x > 1 ==> y == 100 - x + 1; // Adding an implies clause to handle loop entry
{
y := 100 - x;
x := x + 1;
}
assert(y >= 0);
}