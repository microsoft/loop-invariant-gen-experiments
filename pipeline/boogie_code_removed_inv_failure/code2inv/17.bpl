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
invariant m >= 1;
invariant m <= x;
invariant x >= 1;
invariant x <= n;
invariant m >= 1;
invariant m <= x;
invariant 1 <= x;
invariant x <= n + 1;
invariant 1 <= m;
invariant m <= x;
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