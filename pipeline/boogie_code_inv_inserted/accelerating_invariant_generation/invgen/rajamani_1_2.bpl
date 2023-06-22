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
invariant z == 10 * w;
invariant y is an integer;
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
if(y > 10 * w) {
if(z >= 100 * x) {
y := -y;

}

}
}
}
w := w + 1;
z := z + 10;

havoc nondet;
//This comment is for codegen to add havoc nondet
}
if(x >= 4) {
assert(y > 2);

}

}