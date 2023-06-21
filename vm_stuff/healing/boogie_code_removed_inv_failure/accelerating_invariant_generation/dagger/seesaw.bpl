procedure main() {
var nondet: bool;
var nondet_int: int;
var x: int;
var y: int;
if(!(x == 0)) {
return;
}
if(!(y == 0)) {
return;
}
havoc nondet;
while(nondet)
// insert invariants 
invariant x >= 0;
invariant y >= 0;
invariant x >= 0;
invariant y >= 0;
invariant x >= 0;
invariant y >= 0;
{
havoc nondet;
if(nondet) {
if(!(x >= 9)) {
return;
}
x := x + 2;
y := y + 1;

} else {
havoc nondet;
if(nondet) {
if(!(x >= 7)) {
return;
}
if(!(x <= 9)) {
return;
}
x := x + 1;
y := y + 3;

} else {
havoc nondet;
if(nondet) {
if(!(x - 5 >= 0)) {
return;
}
if(!(x - 7 <= 0)) {
return;
}
x := x + 2;
y := y + 1;

} else {
if(!(x - 4 <= 0)) {
return;
}
x := x + 1;
y := y + 2;

}

}

}

havoc nondet;
//This comment is for codegen to add havoc nondet
}
assert(-x + 2 * y >= 0);
assert(3 * x - y >= 0);

}