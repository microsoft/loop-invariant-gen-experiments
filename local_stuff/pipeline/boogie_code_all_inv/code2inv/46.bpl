procedure main() {
var nondet: bool;
var c: int;
var n: int;
c := 0;
assume(n > 0);
havoc nondet;
while(nondet)
// insert invariants 
invariant 0 <= c <= n;
invariant 0 <= c <= n;
invariant 0 <= c <= n;
{
havoc nondet;
if(nondet) {
if(c != n) {
c := c + 1;
}
} else {
if(c == n) {
c := 1;
}
}
}
if(c != n) {
assert(c <= n);
}
}