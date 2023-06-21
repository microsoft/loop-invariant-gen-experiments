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
invariant x >= 0;
invariant y >= 0;
invariant i - x == j - y;
invariant x <= i;
invariant y <= j;
invariant x == 0 || y != 0;
{
x := x - 1;
y := y - 1;
}
if(y != 0) {
assert(i != j);
}
}