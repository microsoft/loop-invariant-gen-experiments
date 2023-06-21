procedure main() {
var nondet: bool;
var lock: int;
var x: int;
var y: int;
y := x + 1;
lock := 0;
while(x != y)
// insert invariants 
invariant (lock == 0) ==> (y == x + 1);
invariant (lock == 1) ==> (y == x);
invariant (lock == 0) ==> (y == x + 1);
invariant (lock == 1) ==> (y == x);
invariant lock == 0 || lock == 1;
{
havoc nondet;
if(nondet) {
lock := 1;
x := y;
} else {
lock := 0;
x := y;
y := y + 1;
}
}
assert(lock == 1);
}