procedure main() {
var nondet: bool;
var i: int;
var j: int;
var x: int;
var y: int;
var z1: int;
var z2: int;
var z3: int;
i := x;
j := y;
while(x != 0)
// insert invariants 
invariant i - x == z1;
invariant j - y == z2;
invariant i - x == j - y;
invariant i - x == j - y;
{
x := x - 1;
y := y - 1;
}
if(i == j) {
assert(y == 0);
}
}