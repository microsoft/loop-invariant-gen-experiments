procedure main() {
var nondet: bool;
var nondet_int: int;
var x1: int;
var x2: int;
var x3: int;
var x4: int;
var x5: int;
if(!(x1 + x2 + x3 + x4 + x5 > 0)) {
return;

}
while(true)
// insert invariants 
invariant x1 >= 0;
invariant x2 >= 0;
invariant x3 >= 0;
invariant x4 >= 0;
invariant x5 >= 0;
{
if(x1 < 0) {
x1 := -x1;
x5 := x5 - x1;
x2 := x2 - x1;

} else {
if(x2 < 0) {
x2 := -x2;
x1 := x1 - x2;
x3 := x3 - x2;

} else {
if(x3 < 0) {
x3 := -x3;
x2 := x2 - x3;
x4 := x4 - x3;

} else {
if(x4 < 0) {
x4 := -x4;
x3 := x3 - x4;
x5 := x5 - x4;

} else {
if(x5 < 0) {
x5 := -x5;
x4 := x4 - x5;
x1 := x1 - x5;

} else {
return;

}
}
}
}
}

}

}