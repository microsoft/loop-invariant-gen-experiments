procedure main() {
var nondet: bool;
var nondet_int: int;
var x: int;
var y: int;
var xa: int;
var ya: int;
xa := 0;
ya := 0;
havoc nondet;
while(nondet)
// insert invariants 
invariant xa >= 0;
invariant ya >= 0;
{
x := xa + 2 * ya;
y := -2 * xa + ya;
x := x + 1;
havoc nondet;
if(nondet) {
y := y + x;
} else {
y := y - x;
}
xa := x - 2 * y;
ya := 2 * x + y;

havoc nondet;
//This comment is for codegen to add havoc nondet
}
assert(xa + 2 * ya >= 0);

}