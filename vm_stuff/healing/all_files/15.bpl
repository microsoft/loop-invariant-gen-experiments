procedure main() {
var nondet: bool;
var x: int;
var m: int;
var n: int;
x := 0;
m := 0;
while(x < n)
// Updated invariants
invariant x >= 0;
invariant m >= 0;
invariant m <= x;
invariant (x == 0) ==> (m == 0);
invariant (n > 0) ==> (x > 0) ==> (m < n); // Strengthened invariant
{
havoc nondet;
if(nondet) {
m := x;
}
x := x + 1;
}
if(n > 0) {
assert(m < n);
}
}