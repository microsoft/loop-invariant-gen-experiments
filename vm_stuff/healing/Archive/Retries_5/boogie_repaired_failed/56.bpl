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
// updated invariants
invariant c >= 0;
invariant c <= n * 2;
invariant (nondet ==> (c == n || c == n + 1 || c == 0));
invariant (!nondet ==> (c >= 1 && c <= n * 2));
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
if(c == n) {
assert(n <= -1);
}
}