procedure main() {
var nondet: bool;
var i: int;
var j: int;
var x: int;
var y: int;
j := 0;
i := 0;
y := 1;
while(i <= x)
// insert invariants 
invariant i >= 0;
invariant j == i * y;
invariant i >= 0;
invariant j == i * y;
invariant i >= 0;
{
i := i + 1;
j := j + y;
}
if(y == 1) {
assert(i == j);
}
}