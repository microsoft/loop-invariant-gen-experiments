procedure main() {
var nondet: bool;
var x: int;
var m: int;
var n: int;
x := 1;
m := 1;
while(x < n)
// insert invariants 
invariant x >= 1;
invariant 1 <= m && m <= x;
invariant x == 1 || m < n;
{
havoc nondet;
if(nondet) {
m := x;
}
x := x + 1;
}
if(n > 1) {
assert(m < n);
}
}