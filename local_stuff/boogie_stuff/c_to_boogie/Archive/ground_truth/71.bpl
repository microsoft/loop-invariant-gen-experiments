procedure main() {
var nondet: bool;
var c: int;
var y: int;
var z: int;
c := 0;
assume(y >= 0);
assume(y >= 127);
z := 36 * y;
havoc nondet;
while(nondet)
// insert invariants 
invariant c >= 0;
invariant z >= 36 * y;
invariant z >= 36 * c;
{
if(c < 36) {
z := z + 1;
c := c + 1;
}
}
if(c < 36) {
assert(z >= 0);
}
}