procedure main() {
var nondet: bool;
var x: int;
var y: int;
var z: int;
x := 0;
while(x < 5)
// insert invariants 
invariant x >= 0;
invariant x <= 5;
invariant x >= 0;
invariant x <= 5;
invariant x >= 0;
invariant x <= 5;
{
x := x + 1;
if(z <= y) {
y := z;
}
}
assert(z >= y);
}