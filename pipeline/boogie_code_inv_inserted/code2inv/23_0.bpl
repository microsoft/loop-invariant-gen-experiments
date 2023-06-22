procedure main() {
var nondet: bool;
var i: int;
var j: int;
i := 1;
j := 20;
while(j >= i)
// insert invariants 
invariant i + j == 22;
{
i := i + 2;
j := j - 1;
}
assert(j == 13);
}