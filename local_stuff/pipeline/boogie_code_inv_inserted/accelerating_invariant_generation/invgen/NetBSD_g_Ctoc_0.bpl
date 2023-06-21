procedure main() {
var nondet: bool;
var nondet_int: int;
var BASE_SZ: int;
var i: int;
var j: int;
var len: int;
len := BASE_SZ;
if(!(BASE_SZ > 0)) {
return;

}
assert(0 <= BASE_SZ - 1);
if(len == 0) {
return;

}
i := 0;
j := 0;
while(true)
// insert invariants 
invariant 0 <= i;
invariant i <= BASE_SZ;
invariant 0 <= j;
invariant j <= BASE_SZ;
invariant len >= 0;
{
if(len == 0) {
return;

} else {
assert(0 <= j);
assert(j < BASE_SZ);
assert(0 <= i);
assert(i < BASE_SZ);
havoc nondet;
if(nondet) {
i := i + 1;
j := j + 1;
return;

}

}
i := i + 1;
j := j + 1;
len := len - 1;

}

}