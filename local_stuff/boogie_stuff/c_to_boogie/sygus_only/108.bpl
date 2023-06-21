procedure main() {
var nondet: bool;
var a: int;
var c: int;
var m: int;
var j: int;
var k: int;
assume(a <= m);
j := 0;
k := 0;
while(k < c)
// insert invariants 
invariant k >= 0;
invariant a <= m;
{
if(m < a) {
m := a;
}
k := k + 1;
}
assert(a <= m);
}