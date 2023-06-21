procedure main() {
var nondet: bool;
var x: int;
var y: int;
x := 1;
while(x < y)
// insert invariants 
invariant x >= 1;
invariant (exists k: int :: k >= 0 && x == 2^k);
invariant x >= y || x * 2 > y;
{
x := x + x;
}
assert(x >= 1);
}