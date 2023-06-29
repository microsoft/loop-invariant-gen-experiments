procedure main() {
var nondet: bool;
var c: int;
var n: int;
var v1: int;
var v2: int;
var v3: int;
c := 0;
assume(n > 0);
havoc nondet;
while(nondet)
// insert invariants 
invariant 0 <= c;
invariant c <= n + 1;
invariant c >= 0;
invariant c <= n + 1;
invariant c != n;
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
if(n > -1) {
assert(c != n);
}
}