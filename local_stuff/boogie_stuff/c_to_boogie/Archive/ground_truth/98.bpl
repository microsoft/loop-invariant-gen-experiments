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
invariant i >= 0;
invariant j >= 0;
invariant j == i * y;
{
i := i + 1;
j := j + y;
}
if(i != j) {
assert(y != 1);
}
}