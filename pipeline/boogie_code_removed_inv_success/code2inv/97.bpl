procedure main() {
var nondet: bool;
var i: int;
var j: int;
var x: int;
var y: int;
j := 0;
i := 0;
y := 2;
while(i <= x)
// insert invariants 
invariant j == 2 * i;
invariant j == i * y;
invariant j == 2 * i;
{
i := i + 1;
j := j + y;
}
if(y == 1) {
assert(i == j);
}
}