procedure main() {
var nondet: bool;
var nondet_int: int;
var x1: int;
var v1: int;
var x2: int;
var v2: int;
var x3: int;
var v3: int;
var t: int;
x1 := 100;
x2 := 75;
x3 := -50;
if(!(v3 >= 0)) {
return;
}
if(!(v1 <= 5)) {
return;
}
if(!(v1 - v3 >= 0)) {
return;
}
if(!(2 * v2 - v1 - v3 == 0)) {
return;
}
t := 0;
if(!(v2 + 5 >= 0)) {
return;
}
if(!(v2 <= 5)) {
return;
}
havoc nondet;
while(nondet)
// insert invariants 
invariant v1 <= 5;
invariant v2 + 5 >= 0;
invariant v2 <= 5;
invariant v3 >= 0;
invariant 2 * v2 - v1 - v3 == 0;
invariant v1 <= 5;
invariant v2 + 5 >= 0;
invariant v2 <= 5;
invariant v3 >= 0;
invariant 2 * v2 - v1 - v3 == 0;
invariant v1 <= 5;
invariant v3 >= 0;
invariant 2 * v2 - v1 - v3 == 0;
invariant v2 + 6 >= 0;
invariant v2 <= 6;
invariant x2 + 5 * t >= 75;
invariant 5 * t + 75 >= x2;
invariant v1 - 2 * v2 + v3 + 2 * t >= 0;
invariant v1 - v3 >= 0;
{
if(!(v2 + 5 >= 0)) {
return;
}
if(!(v2 <= 5)) {
return;
}
havoc nondet;
if(nondet) {
if(!(2 * x2 - x1 - x3 >= 0)) {
return;
}
x1 := x1 + v1;
x3 := x3 + v3;
x2 := x2 + v2;
v2 := v2 - 1;
t := t + 1;

} else {
if(!(2 * x2 - x1 - x3 <= 0)) {
return;
}
x1 := x1 + v1;
x3 := x3 + v3;
x2 := x2 + v2;
v2 := v2 + 1;
t := t + 1;

}

havoc nondet;
//This comment is for codegen to add havoc nondet
}
assert(v1 <= 5);
assert(2 * v2 + 2 * t >= v1 + v3);
assert(5 * t + 75 >= x2);
assert(v2 <= 6);
assert(v3 >= 0);
assert(v2 + 6 >= 0);
assert(x2 + 5 * t >= 75);
assert(v1 - 2 * v2 + v3 + 2 * t >= 0);
assert(v1 - v3 >= 0);

}