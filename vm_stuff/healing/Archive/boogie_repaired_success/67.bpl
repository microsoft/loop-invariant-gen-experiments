procedure main() {
var nondet: bool;
var n: int;
var y: int;
var x: int;
x := 1;
while(x <= n)
invariant x > 1 ==> y >= 0;
{
y := n - x;
x := x + 1;
}
if(n > 0) {
assert(y >= 0);
}
}