procedure main() {
var nondet: bool;
var nondet_int: int;
var x: int;
var n: int;
x := 0;
assume(n > 0);
while(x < n)
// insert invariants 
invariant x <= n;
invariant n > 0;
{
x := x + 1;

}
assert(x <= n);

}