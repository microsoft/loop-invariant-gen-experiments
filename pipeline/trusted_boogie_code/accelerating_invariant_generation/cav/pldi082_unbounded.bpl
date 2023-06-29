procedure main() {
var nondet: bool;
var nondet_int: int;
var x: int;
var y: int;
var N: int;
x := 0;
y := 0;
if(N < 0) {
return;
}
while(true)
// insert invariants 
{
if(x <= N) {
y := y + 1;
} else {
if(x >= N + 1) {
y := y - 1;
} else {
return;
}
}
if(y < 0) {
break;
}
x := x + 1;

}
assert(!((N >= 0) && (y == -1) && (x >= 2 * N + 3)));

}
