procedure main() {
var nondet: bool;
var i: int;
var j: int;
var k: int;
var n: int;
assume(k >= 0);
assume(n >= 0);
i := 0;
j := 0;
while(i <= n)
invariant i >= 0;
invariant (i == 0 && j == 0) || (i > 0 && j == (i * (i - 1)) div 2);
invariant 0 <= i <= n;
invariant j >= 0;
invariant k >= i && (i == 0 ==> k >= 0); // Modified invariant
{
i := i + 1;
j := j + i;
}
assert(i + j + k > 2 * n);
}