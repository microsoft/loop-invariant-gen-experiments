procedure main() {
var nondet: bool;
var i: int;
var x: int;
var y: int;
i := 0;
assume(x >= 0);
assume(y >= 0);
assume(x >= y);
havoc nondet;
while(nondet)
// insert invariants 
invariant i >= 0;
invariant i <= x;
invariant (i < y) || (i <= y);
{
if(i < y) {
i := i + 1;
}
}
if(i >= x) {
if(0 > i) {
assert(i >= y);
}
}
}