 procedure main()
{
var i: int;
var j: int;
var x: int;
var y: int;
// pre-conditions
assume(j == 0);
assume(i == 0);
assume(y == 1);
// loop body
while (i <= x)
invariant j == i * y;
{
i := i + 1;
j := j + y;
}
// post-condition
if (i != j)
{
assert(y != 1);
}
}