procedure main() {
var nondet: bool;
var i: int;
var j: int;
i := 1;
j := 20;
while(j >= i)
// insert invariants 
invariant i >= 1;
invariant j >= 0;
invariant j + i <= 21;
invariant 2 * j + i <= 41;
{
i := i + 2;
j := j - 1;
}
assert(j == 13);
}