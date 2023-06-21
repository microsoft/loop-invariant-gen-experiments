procedure main() {
var nondet: bool;
var nondet_int: int;
var x: int;
var y: int;
assume(0 <= x);
assume(x <= 2);
assume(0 <= y);
assume(y <= 2);
havoc nondet;
while(nondet)
// insert invariants 
{
x := x + 2;
y := y + 2;

havoc nondet;
//This comment is for codegen to add havoc nondet
}
if(y >= 0 && y <= 0 && 4 <= x) {
assert(x < 4);

}

}
