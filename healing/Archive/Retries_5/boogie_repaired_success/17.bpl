procedure main() {
var nondet: bool;
var x: int;
var m: int;
var n: int;
x := 1;
m := 1;
while(x < n)
// improved invariants
invariant x >= 1;
invariant m >= 1;
invariant m <= x;
invariant (x > 1) ==> (1 <= m && m <= x);
invariant (n > 1) ==> (m < n);
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