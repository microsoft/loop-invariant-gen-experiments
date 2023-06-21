procedure main() {
var nondet: bool;
var nondet_int: int;
var x: int;
var y: int;
var z: int;
var w: int;
x := 0;
y := 0;
z := 0;
w := 0;
havoc nondet;
while(nondet)
// insert invariants 
invariant x >= 0;
invariant y % 2 == 0;
invariant z % 2 == 0;
invariant w % 2 == 0;
invariant z == w;
{
havoc nondet;
if(nondet) {
x := x + 1;
y := y + 2;

} else {
havoc nondet;
if(nondet) {
if(x >= 4) {
x := x + 1;
y := y + 3;
z := z + 10;
w := w + 10;

}

} else {
if(x >= z && w >= y + 1) {
x := -x;
y := -y;

}
}
}
x := x;

havoc nondet;
//This comment is for codegen to add havoc nondet
}
assert(!(3 * x <= y - 1));

}