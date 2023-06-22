procedure main() {
var nondet: bool;
var i: int;
var j: int;
var x: int;
var y: int;
i := x;
j := y;
while(x != 0)
// insert invariants 
invariant y == j - i + x;
invariant y == j - (i - x);
invariant i - x == j - y;
invariant x >= 0;
{
x := x - 1;
y := y - 1;
}
if(i == j) {
assert(y == 0);
}
}