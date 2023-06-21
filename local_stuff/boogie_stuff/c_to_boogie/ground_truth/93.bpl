procedure main() {
var nondet: bool;
var i: int;
var n: int;
var x: int;
var y: int;
assume(n >= 0);
i := 0;
x := 0;
y := 0;
while(i < n)
// insert invariants 
invariant 3 * i == x + y;
invariant i <= n;
{
i := i + 1;
havoc nondet;
if(nondet) {
x := x + 1;
y := y + 2;
} else {
x := x + 2;
y := y + 1;
}
}
assert(3 * n == x + y);
}