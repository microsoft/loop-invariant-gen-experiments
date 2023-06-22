procedure main() {
var nondet: bool;
var nondet_int: int;
var x1: int;
var x2: int;
var x3: int;
var d1: int;
var d2: int;
var d3: int;
var c1: bool;
var c2: bool;
havoc nondet_int;
x1 := nondet_int;
havoc nondet_int;
x2 := nondet_int;
havoc nondet_int;
x3 := nondet_int;
d1 := 1;
d2 := 1;
d3 := 1;
havoc nondet;
c1 := nondet;
havoc nondet;
c2 := nondet;
assume(x1 >= 0);
assume(x2 >= 0);
assume(x3 >= 0);
while(x1 > 0 && x2 > 0 && x3 > 0)
// insert invariants 
invariant x1 >= 0;
invariant x2 >= 0;
invariant x3 >= 0;
{
if(c1) {
x1 := x1 - d1;
} else {
if(c2) {
x2 := x2 - d2;
} else {
x3 := x3 - d3;
}
}
havoc nondet;
c1 := nondet;
havoc nondet;
c2 := nondet;

}
assert(x1 == 0 && x2 == 0 && x3 == 0);

}