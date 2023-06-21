 procedure main()
{
var x: int;
var y: int;
var z1: int;
var z2: int;
var z3: int;
// pre-conditions
x := -15000;
// loop body
while (x < 0)
invariant y >= 0;
{
x := x + y;
y := y + 1;
}
// post-condition
assert(y > 0);
}