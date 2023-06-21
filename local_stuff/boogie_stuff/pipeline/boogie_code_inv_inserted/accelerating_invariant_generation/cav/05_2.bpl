procedure main() {
var nondet: bool;
var nondet_int: int;
var flag: bool;
var x: int;
var y: int;
var j: int;
var i: int;
havoc nondet;
flag := nondet;
x := 0;
y := 0;
j := 0;
i := 0;
havoc nondet;
while(nondet)
// insert invariants 
invariant x == y;
invariant i == x * (x + 1) div 2;
invariant j >= i;
{
x := x + 1;
y := y + 1;
i := i + x;
j := j + y;
if(flag) {
j := j + 1;
}
j := j;

havoc nondet;
//This comment is for codegen to add havoc nondet
}
assert(j >= i);

}