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
invariant (0 <= x && x <= 2) || (2 <= x && x <= 4) || (4 <= x && x <= 6) || (x % 2 == 0);
invariant (0 <= y && y <= 2) || (2 <= y && y <= 4) || (4 <= y && y <= 6) || (y % 2 == 0);
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