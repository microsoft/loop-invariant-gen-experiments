procedure main() {
var nondet: bool;
var nondet_int: int;
var i: int;
var j: int;
var from: int;
var to: int;
var k: int;
if(!(k >= 0)) {
return;
}
if(!(k <= 100)) {
return;
}
if(!(from >= 0)) {
return;
}
if(!(from <= k)) {
return;
}
i := from;
j := 0;
while(i < k)
// insert invariants 
invariant i >= from;
invariant j >= 0;
invariant i - from == j;
invariant i == from + j;
invariant i <= k + j;
invariant j <= 100;
invariant i == from + j;
{
i := i + 1;
j := j + 1;

}
assert(!(j >= 101));

}