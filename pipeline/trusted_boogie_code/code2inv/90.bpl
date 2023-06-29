procedure main() {
var nondet: bool;
var lock: int;
var v1: int;
var v2: int;
var v3: int;
var x: int;
var y: int;
y := x + 1;
lock := 0;
while(x != y)
// insert invariants 
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