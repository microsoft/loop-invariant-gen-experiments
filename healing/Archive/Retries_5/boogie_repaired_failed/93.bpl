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
invariant i == 0 ==> (x == 0 && y == 0); // added to hold on loop entry
invariant i > 0 ==> (3 * i == x + y); // changed to hold conditionally after loop entry
invariant (x - y) <= 2 && (y - x) <= 2;
invariant x >= 0 && y >= 0;
invariant (x % 2 == 0 && y % 2 == 1) || (x % 2 == 1 && y % 2 == 0); // already tracking x and y's relationship with i
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