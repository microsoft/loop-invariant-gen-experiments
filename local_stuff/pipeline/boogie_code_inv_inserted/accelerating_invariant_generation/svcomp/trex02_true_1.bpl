procedure main() {
var nondet: bool;
var nondet_int: int;
var x: int;
var c: bool;
havoc nondet_int;
x := nondet_int;
while(x > 0)
// insert invariants 
invariant x >= 0; // x is always non-negative
{
havoc nondet;
c := nondet;
if(c) {
x := x - 1;
} else {
x := x - 1;
}

}
assert(x <= 0);

}