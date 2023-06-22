procedure main() {
var nondet: bool;
var nondet_int: int;
var x: int;
var y: int;
var z: int;
var tmp: bool;
havoc nondet_int;
x := nondet_int;
havoc nondet_int;
y := nondet_int;
havoc nondet_int;
z := nondet_int;
while(x < 100 && 100 < z)
// insert invariants 
invariant (x < 100 && 100 < z) || (x >= 100) || (z <= 100);
{
havoc nondet;
tmp := nondet;
if(tmp) {
x := x + 1;

} else {
x := x - 1;
z := z - 1;

}

}
assert(false);

}