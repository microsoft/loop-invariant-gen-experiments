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
invariant (x == 1 || n <= 1 || (1 <= x && x <= n));
invariant (m == 1 || n <= 1 || (1 <= m && m <= x));
invariant (m < n || n <= 1 || (nondet && m == n - 1));
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