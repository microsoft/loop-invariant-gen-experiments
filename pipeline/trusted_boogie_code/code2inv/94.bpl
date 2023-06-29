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
{
i := i + 1;
j := j + i;
}
assert(i + j + k > 2 * n);
}