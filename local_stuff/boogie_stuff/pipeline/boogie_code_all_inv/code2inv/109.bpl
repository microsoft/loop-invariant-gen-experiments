procedure main() {
var nondet: bool;
var a: int;
var c: int;
var m: int;
var j: int;
var k: int;
j := 0;
k := 0;
while(k < c)
// insert invariants 
invariant k >= 0;
invariant k <= c;
invariant (m >= a) || (m < a && k == 0);
invariant k >= 0;
invariant k <= c;
invariant (m >= a) || (m < a && k == 0);
invariant k >= 0;
invariant k <= c;
invariant m >= a || (m < a && k == 0);
{
if(m < a) {
m := a;
}
k := k + 1;
}
if(c > 0) {
assert(a <= m);
}
}