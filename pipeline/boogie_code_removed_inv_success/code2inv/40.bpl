procedure main() {
var nondet: bool;
var c: int;
var n: int;
c := 0;
assume(n > 0);
havoc nondet;
while(nondet)
// insert invariants 
invariant c >= 0;
invariant c >= 0;
invariant c <= n + 1;
invariant 0 <= c;
invariant c <= n;
{
havoc nondet;
if(nondet) {
if(c > n) {
c := c + 1;
}
} else {
if(c == n) {
c := 1;
}
}
}
if(c != n) {
assert(c >= 0);
}
}