procedure main() {
var nondet: bool;
var x: int;
x := 0;
while(x < 100)
// insert invariants 
invariant x >= 0;
invariant x <= 100;
invariant x >= 0;
invariant x <= 100;
invariant x >= 0;
invariant x <= 100;
{
x := x + 1;
}
assert(x == 100);
}