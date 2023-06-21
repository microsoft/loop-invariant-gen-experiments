procedure main() {
var nondet: bool;
var x: int;
var m: int;
var n: int;
x := 0;
m := 0;
while(x < n)
invariant (x == 0) ==> (m == 0);
invariant 0 <= m && m <= x;
invariant (x > 0) ==> (m >= 0 && m <= n);
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