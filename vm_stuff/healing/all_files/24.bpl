procedure main() {
var nondet: bool;
var i: int;
var j: int;
i := 1;
j := 10;
while(j >= i)
invariant i >= 1;
invariant i mod 2 == 1;
invariant j <= 10;
invariant j >= 0;
invariant j == 10 - ((i - 1) div 2);
invariant i <= 9; // added new invariant
{
i := i + 2;
j := j - 1;
}
assert(j == 6);
}