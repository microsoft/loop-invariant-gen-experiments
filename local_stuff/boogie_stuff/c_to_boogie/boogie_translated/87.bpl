procedure main() {
var nondet: bool;
var lock: int;
var x: int;
var y: int;
x := y;
lock := 1;
while(x != y)
// insert invariants 
invariant lock == 1 || lock == 0;
invariant (lock == 1) ==> (x == y);
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