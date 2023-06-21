procedure main() {
var nondet: bool;
var c: int;
var n: int;
c := 0;
assume(n > 0);
havoc nondet;
while(nondet)
invariant 0 <= c && c <= n;
invariant (c != n) ==> (c >= 0 && c < n);
invariant (c != n) ==> (c < n);
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