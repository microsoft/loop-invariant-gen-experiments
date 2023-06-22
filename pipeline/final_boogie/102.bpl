procedure main() {
var nondet: bool;
var n: int;
var x: int;
x := 0;
while(x < n)
invariant x >= 0;
invariant (n < 0) || (x <= n);
{
x := x + 1;
}
if(n >= 0) {
assert(x == n);
}
}