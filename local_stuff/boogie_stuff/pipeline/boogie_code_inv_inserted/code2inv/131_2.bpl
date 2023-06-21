procedure main() {
var nondet: bool;
var d1: int;
var d2: int;
var d3: int;
var x1: int;
var x2: int;
var x3: int;
d1 := 1;
d2 := 1;
d3 := 1;
x1 := 1;
while(x1 > 0)
// insert invariants 
invariant x1 >= 0;
{
if(x2 > 0) {
if(x3 > 0) {
x1 := x1 - d1;
x2 := x2 - d2;
x3 := x3 - d3;
}
}
}
assert(x3 >= 0);
}