procedure main() {
var nondet: bool;
var z1: int;
var z2: int;
var z3: int;
var x: int;
var m: int;
var n: int;
x := 1;
m := 1;
while(x < n)
invariant n <= 1 || 1 <= x <= n;
invariant n <= 1 || 1 <= m <= x;
invariant x == 1 || (forall k: int :: (1 <= k < x) ==> (z1 + z2 <= k * z3 ==> m >= k));
invariant (nondet ==> m == x - 1) && (!nondet ==> m == 1);
invariant m < n || n <= 1 || (nondet && m == n - 1);
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