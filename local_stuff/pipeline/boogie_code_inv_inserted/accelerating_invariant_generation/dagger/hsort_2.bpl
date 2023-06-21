procedure main() {
var nondet: bool;
var nondet_int: int;
var n: int;
var l: int;
var r: int;
var i: int;
var j: int;
if(!(n >= 2)) {
return;
}
if(!(r - n == 0)) {
return;
}
if(!(i - l == 0)) {
return;
}
if(!(j - 2 * l == 0)) {
return;
}
if(!(2 * l - n >= 0)) {
return;
}
if(!(2 * l - n - 1 <= 0)) {
return;
}
havoc nondet;
while(nondet)
// insert invariants 
invariant 2*i - j == 0;
invariant -2*l + r >= -1;
invariant -2*l + 3*r - 2*i >= 0;
invariant -l + i >= 0;
invariant r >= 2;
invariant l >= 1;
invariant n - r >= 0;
{
havoc nondet;
if(nondet) {
if(!(r - j - 1 >= 0)) {
return;
}
i := j + 1;
j := 2 * j + 2;

} else {
havoc nondet;
if(nondet) {
if(!(j - r <= 0)) {
return;
}
i := j;
j := 2 * j;

} else {
havoc nondet;
if(nondet) {
if(!(l >= 2)) {
return;
}
if(!(r >= 2)) {
return;
}
i := l - 1;
j := 2 * l - 2;
l := l - 1;

} else {
if(!(l <= 1)) {
return;
}
r := r - 1;
if(!(r >= 3)) {
return;
}
i := l;
j := 2 * l;

}

}

}

havoc nondet;
//This comment is for codegen to add havoc nondet
}
assert(2 * i - j >= 0);
assert(2 * i - j <= 0);
assert(-2 * l + r + 1 >= 0);
assert(r - 2 >= 0);
assert(l - 1 >= 0);
assert(n - r >= 0);

}