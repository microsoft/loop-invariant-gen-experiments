procedure main() {
var nondet: bool;
var x: int;
var m: int;
var n: int;
x := 1;
m := 1;
while(x < n)
// insert invariants 
invariant 1 <= m;
invariant m <= x;
invariant m == 1 || (m == x && unknown); // loop invariant
{
havoc nondet;
if(nondet) {
m := x;
}
x := x + 1;
}
if(n > 1) {
assert(m >= 1);
}
}