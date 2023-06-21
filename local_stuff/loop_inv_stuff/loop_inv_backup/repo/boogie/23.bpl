 procedure main()
{
var i: int;
var j: int;
// pre-conditions
assume(i == 1);
assume(j == 20);
// loop body
while (j >= i)
invariant j + i == 21;
{
i := i + 2;
j := j - 1;
}
// post-condition
assert(j == 13);
}