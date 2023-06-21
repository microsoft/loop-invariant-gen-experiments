procedure main() {
var nondet: bool;
var v1: int;
var v2: int;
var v3: int;
var x: int;
var size: int;
var y: int;
var z: int;
x := 0;
while(x < size)
// insert invariants
invariant x >= 0;
invariant x == 0 || y <= z;
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