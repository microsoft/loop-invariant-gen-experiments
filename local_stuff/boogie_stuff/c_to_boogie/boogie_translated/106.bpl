procedure main() {
var nondet: bool;
var a: int;
var m: int;
var j: int;
var k: int;
assume(a <= m);
assume(j < 1);
k := 0;
while(k < 1)
// insert invariants 
invariant k >= 0;
invariant a <= m;
{
if(m < a) {
m := a;
}
k := k + 1;
}
assert(a >= m);
}