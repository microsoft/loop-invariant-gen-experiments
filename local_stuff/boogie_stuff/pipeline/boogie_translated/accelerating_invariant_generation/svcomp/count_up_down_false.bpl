procedure main() {
var nondet: bool;
var nondet_int: int;
var n: int;
var x: int;
var y: int;
havoc nondet_int;
n := nondet_int;
assume(n >= 0);
x := n;
y := 0;
while(x > 0)
// insert invariants 
{
x := x - 1;
y := y + 1;

}
assert(y != n);

}
