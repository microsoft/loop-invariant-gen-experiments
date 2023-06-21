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
while(true)
// insert invariants 
invariant x == 0;
invariant y == 0;
invariant n > 0;
invariant x == 0;
invariant y == 0;
invariant n > 0;
invariant x == 0;
invariant y == 0;
invariant n > 0;
{
assert(x == 0);
i := i + 1;

}
assert(x != 0);

}