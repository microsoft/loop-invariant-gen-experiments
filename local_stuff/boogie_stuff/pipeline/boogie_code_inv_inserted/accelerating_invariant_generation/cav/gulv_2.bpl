procedure main() {
var nondet: bool;
var nondet_int: int;
var x: int;
var y: int;
var w: int;
var z: int;
x := 0;
y := 0;
w := 0;
z := 0;
havoc nondet;
while(nondet)
// insert invariants 
invariant x >= 0;
invariant y >= -100 * x;
invariant w >= 0;
invariant z == 10 * w;
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

} else {
if(y > 10 * w && z >= 100 * x) {
y := -y;

}
}
}
w := w + 1;
z := z + 10;
x := x;

havoc nondet;
//This comment is for codegen to add havoc nondet
}
assert(!(x >= 4 && y <= 2));

}