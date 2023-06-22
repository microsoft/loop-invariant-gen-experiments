procedure main() {
var nondet: bool;
var nondet_int: int;
var x: int;
x := 0;
havoc nondet;
if(nondet) {
x := x + 1;
} else {
x := x + 22;
}
havoc nondet;
if(nondet) {
x := x + 1;
} else {
x := x + 20;
}
havoc nondet;
if(nondet) {
x := x + 1;
} else {
x := x + 18;
}
havoc nondet;
if(nondet) {
x := x + 1;
} else {
x := x + 16;
}
havoc nondet;
if(nondet) {
x := x + 1;
} else {
x := x + 14;
}
havoc nondet;
if(nondet) {
x := x + 1;
} else {
x := x + 12;
}
havoc nondet;
if(nondet) {
x := x + 1;
} else {
x := x + 10;
}
havoc nondet;
if(nondet) {
x := x + 1;
} else {
x := x + 8;
}
havoc nondet;
if(nondet) {
x := x + 1;
} else {
x := x + 6;
}
havoc nondet;
if(nondet) {
x := x + 1;
} else {
x := x + 4;
}
havoc nondet;
if(nondet) {
x := x + 1;
} else {
x := x + 2;
}
assert(x <= 132);

}
