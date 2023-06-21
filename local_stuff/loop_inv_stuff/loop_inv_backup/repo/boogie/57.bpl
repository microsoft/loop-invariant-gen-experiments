 procedure main()
{
var c: int;
var n: int;
var v1: int;
var v2: int;
var v3: int;
var nondet: bool;
// pre-conditions
c := 0;
assume(n > 0);
// loop body
havoc nondet;
while (nondet)
invariant 0 <= c && c <= n+1;
{
havoc nondet;
if (nondet) {
if (c > n) {
c := c + 1;
}
} else {
if (c == n) {
c := 1;
}
}
}
// post-condition
if(n > -1) {
assert(c != n);
}
}