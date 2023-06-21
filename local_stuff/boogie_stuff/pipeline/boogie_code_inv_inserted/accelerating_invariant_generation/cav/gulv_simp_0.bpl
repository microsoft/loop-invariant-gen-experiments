procedure main() {
var nondet: bool;
var nondet_int: int;
var x: int;
var y: int;
x := 0;
y := 0;
havoc nondet;
while(nondet)
// insert invariants 
invariant x >= 0;
invariant y >= 0;
invariant y == 100 * x;
{
havoc nondet;
if(nondet) {
x := x + 1;
y := y + 100;

} else {
havoc nondet;
if(nondet) {
if(x >= 4) {
x := x + 1;
y := y + 1;

}

}
}
x := x;

havoc nondet;
//This comment is for codegen to add havoc nondet
}
assert(!(x >= 4 && y <= 2));

}