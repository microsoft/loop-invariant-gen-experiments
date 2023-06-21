procedure main() {
var nondet: bool;
var x: int;
var m: int;
var n: int;
x := 0;
m := 0;
while(x < n)
// fixed invariants
invariant 0 <= x <= n;
invariant (x == 0) ==> (m == 0);
invariant (x > 0) ==> (0 <= m <= x);
invariant (x == n) ==> (m >= 0);
invariant (m <= x); // added invariant
{
havoc nondet;
if(nondet) {
m := x;
}
x := x + 1;
}
if(n > 0) {
assert(m >= 0);
}
}