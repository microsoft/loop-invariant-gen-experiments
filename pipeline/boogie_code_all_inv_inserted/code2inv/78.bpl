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
invariant i <= y;
invariant i >= 0;
invariant x >= 0;
invariant y >= 0;
invariant x >= y;
invariant i <= y;
invariant i >= 0;
invariant i <= y;
invariant x >= 0;
invariant y >= 0;
invariant x >= y;
{
if(i < y) {
i := i + 1;
}
}
if(i < y) {
assert(0 <= i);
}
}