procedure main() {
var nondet: bool;
var i: int;
var j: int;
i := 1;
j := 20;
while(j >= i)
// updated invariants
invariant (j == 20 - ((i - 1) div 2)) && (j >= 13);
{
i := i + 2;
j := j - 1;
}
assert(j == 13);
}