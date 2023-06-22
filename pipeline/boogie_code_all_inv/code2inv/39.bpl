procedure main() {
var nondet: bool;
var n: int;
var c: int;
c := 0;
assume(n > 0);
havoc nondet;
while(nondet)
// insert invariants 
invariant 1 <= c;
invariant c <= n;
invariant 1 <= c;
invariant c <= n;
invariant 1 <= c;
invariant c <= n;
{
if(c == n) {
c := 1;
} else {
c := c + 1;
}
}
if(c == n) {
assert(c <= n);
}
}