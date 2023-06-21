procedure main() {
var nondet: bool;
var i: int;
var j: int;
i := 1;
j := 10;
while(j >= i)
// fixed invariants
invariant i >= 1;
invariant i % 2 == 1;
invariant j >= i;
invariant j <= 10;
invariant j >= 6;
invariant j == 10 - ((i - 1) / 2);
{
i := i + 2;
j := j - 1;
}
assert(j == 6);
}