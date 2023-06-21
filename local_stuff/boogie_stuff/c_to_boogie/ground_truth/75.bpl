procedure main() {
var nondet: bool;
var c: int;
var x1: int;
var x2: int;
var x3: int;
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
invariant c <= 36;
invariant z >= 36 * y;
invariant z <= 36 * y + c;
invariant c == 0 || c == 36 || z < 4608;
{
if(c < 36) {
z := z + 1;
c := c + 1;
}
}
if(c < 36) {
assert(z < 4608);
}
}