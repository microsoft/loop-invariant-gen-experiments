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
invariant i >= 0;
invariant n >= 0;
invariant i <= n;
invariant (i == 0) ==> (x == 0 && y == 0);
invariant (i <= n) ==> (3 * i == x + y);
invariant x >= 0 && y >= 0;
invariant (i > 0) ==> (x > 0 || y > 0);
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