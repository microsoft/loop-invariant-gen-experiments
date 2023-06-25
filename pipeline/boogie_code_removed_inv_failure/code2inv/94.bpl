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
// insert invariants 
invariant i >= 0;
invariant j == (i * (i - 1)) div 2;
invariant 0 <= i <= n + 1;
invariant i >= 0;
invariant j == (i * (i - 1)) div 2;
invariant i <= n + 1;
invariant i >= 0;
invariant j == (i * (i - 1)) div 2;
invariant i <= n + 1;
{
i := i + 1;
j := j + i;
}
assert(i + j + k > 2 * n);
}