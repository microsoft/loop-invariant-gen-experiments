procedure main() {
var nondet: bool;
var x: int;
var size: int;
var y: int;
var z: int;
x := 0;
while(x < size)
// insert invariants
invariant x >= 0;
invariant x == 0 || x <= size;
invariant (x == 0) || (y <= z) || (x > 0 && nondet);
invariant x == 0 || z >= y;
{
x := x + 1;
if(z <= y) {
y := z;
}
}
if(size > 0) {
assert(z >= y);
}
}