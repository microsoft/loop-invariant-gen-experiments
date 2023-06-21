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
{
i := i + 1;
j := j + y;
}
if(i != j) {
assert(y != 1);
}
}