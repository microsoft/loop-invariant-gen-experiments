 procedure main()
{
var c: int;
var y: int;
var z: int;
var nondet: bool;
// pre-conditions
c := 0;
assume(y >= 0);
assume(y >= 127);
z := 36 * y;
// loop body
havoc nondet;
while (nondet)
invariant z >= 36*y && z <= 36*y + 36 && c >= 0 && c <= 36;
{
havoc nondet;
if (c < 36) {
z := z + 1;
c := c + 1;
}
}
// post-condition
if (z < 0)
if (z >= 4608) {
assert(c >= 36);
}
}