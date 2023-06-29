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
invariant (i - x) == (j - y);
invariant i - j == x - y;
invariant i - j == x - y;
{
x := x - 1;
y := y - 1;
}
if(y != 0) {
assert(i != j);
}
}