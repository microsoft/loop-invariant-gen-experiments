procedure main() {
var nondet: bool;
var nondet_int: int;
var i: int;
var j: int;
var x: int;
var y: int;
x := i;
y := j;
while(x != 0)
// insert invariants 
{
x := x - 1;
y := y - 1;

}
if((i == j) && (y != 0)) {
assert(false);

}

}
