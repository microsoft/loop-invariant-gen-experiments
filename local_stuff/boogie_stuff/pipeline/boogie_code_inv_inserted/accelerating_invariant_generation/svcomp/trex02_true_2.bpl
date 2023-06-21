procedure main() {
var nondet: bool;
var nondet_int: int;
var x: int;
var c: bool;
havoc nondet_int;
x := nondet_int;
while(x > 0)
// insert invariants 
invariant (x == unknown_int() - n) && (x > 0) || (x == unknown_int() - n) && (x <= 0);
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