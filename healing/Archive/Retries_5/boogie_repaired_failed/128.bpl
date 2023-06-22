procedure main() {
var nondet: bool;
var x: int;
var y: int;
x := 1;
while(x < y)
invariant x >= 1;
invariant x == 1 || (exists k: int :: (k >= 0 && x == 2^k));
invariant y >= 0;
{
x := x + x;
}
assert(x >= 1);
}