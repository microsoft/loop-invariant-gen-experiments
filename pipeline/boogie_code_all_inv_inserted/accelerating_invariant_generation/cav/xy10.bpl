procedure main() {
var nondet: bool;
var nondet_int: int;
var x: int;
var y: int;
var z: int;
x := 0;
y := 0;
havoc nondet;
while(nondet)
// insert invariants 
invariant x >= 0;
invariant y >= 0;
invariant x == 10 * y;
invariant x >= 0;
invariant y >= 0;
invariant x == 10 * y;
invariant x >= 0;
invariant y >= 0;
invariant x == 10 * y;
{
x := x + 10;
y := y + 1;

havoc nondet;
//This comment is for codegen to add havoc nondet
}
assert(!(x <= z && y >= z + 1));

}