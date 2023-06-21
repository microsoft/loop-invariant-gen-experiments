procedure main() {
var nondet: bool;
var nondet_int: int;
var x1: int;
var x2: int;
var x3: int;
var x4: int;
var x5: int;
var x6: int;
var x7: int;
var p: int;
var q: int;
x1 := 0;
x2 := 0;
x3 := 0;
x4 := 0;
x5 := 0;
if(!(x6 == p)) {
return;
}
if(!(x7 == q)) {
return;
}
if(!(p >= 1)) {
return;
}
if(!(q >= 1)) {
return;
}
havoc nondet;
while(nondet)
// insert invariants 
invariant x1 >= 0;
invariant x2 >= 0;
invariant x3 >= 0;
invariant x4 >= 0;
invariant x5 >= 0;
invariant x6 >= 0;
invariant x7 >= 0;
invariant x1 + x2 + x4 + x5 + x6 == p;
invariant x2 + x3 + x4 + x7 == q;
{
havoc nondet;
if(nondet) {
if(!(x6 >= 1)) {
return;
}
x1 := x1 + 1;
x6 := x6 - 1;

} else {
havoc nondet;
if(nondet) {
if(!(x1 >= 1)) {
return;
}
if(!(x7 >= 1)) {
return;
}
x1 := x1 - 1;
x2 := x2 + 1;
x7 := x7 - 1;

} else {
havoc nondet;
if(nondet) {
if(!(x2 >= 1)) {
return;
}
x2 := x2 - 1;
x3 := x3 + 1;
x6 := x6 + 1;

} else {
havoc nondet;
if(nondet) {
if(!(x3 >= 1)) {
return;
}
if(!(x6 >= 1)) {
return;
}
x3 := x3 - 1;
x4 := x4 + 1;
x6 := x6 - 1;

} else {
havoc nondet;
if(nondet) {
if(!(x4 >= 1)) {
return;
}
x4 := x4 - 1;
x5 := x5 + 1;
x7 := x7 + 1;

} else {
if(!(x5 >= 1)) {
return;
}
x5 := x5 - 1;
x6 := x6 + 1;

}

}

}

}

}

havoc nondet;
//This comment is for codegen to add havoc nondet
}
assert(x2 + x3 + x4 + x7 == q);
assert(x2 + x3 + x4 + x7 >= q);
assert(x1 + x2 + x4 + x5 + x6 >= p);
assert(x1 + x2 + x4 + x5 + x6 <= p);
assert(x7 >= 0);
assert(x6 >= 0);
assert(x5 >= 0);
assert(x4 >= 0);
assert(x3 >= 0);
assert(x2 >= 0);
assert(x1 >= 0);
assert(x2 + x3 + x4 + x7 >= 1);
assert(x1 + x2 + x4 + x5 + x6 >= 1);
assert(x1 + x2 + x4 + x6 + x7 >= 1);

}