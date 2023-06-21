procedure main() {
var nondet: bool;
var i: int;
var j: int;
i := 1;
j := 10;
while(j >= i)
// insert invariants 
invariant i >= 1;
invariant j <= 10;
invariant (j - i) mod 3 == 0;
{
i := i + 2;
j := j - 1;
}
assert(j == 6);
}