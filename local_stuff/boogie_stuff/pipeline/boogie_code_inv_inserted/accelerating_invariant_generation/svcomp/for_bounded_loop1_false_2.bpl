procedure main() {
var nondet: bool;
var nondet_int: int;
var i: int;
var x: int;
var y: int;
var n: int;
i := 0;
x := 0;
y := 0;
havoc nondet_int;
n := nondet_int;
assume(n > 0);
i := 0;
while(i < n)
// insert invariants 
invariant i >= 0;
invariant i <= n;
invariant (x == 0) || (x != 0);
{
x := x - y;
assert(x == 0);
havoc nondet_int;
y := nondet_int;
assume(y != 0);
x := x + y;
assert(x != 0);
i := i + 1;

}
assert(x == 0);

}