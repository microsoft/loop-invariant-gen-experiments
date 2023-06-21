procedure main() {
var nondet: bool;
var nondet_int: int;
var n: int;
var m: int;
var i: int;
i := 1;
while(i < n)
// insert invariants 
invariant i >= 1;
invariant i > 0;
{
if(m > 0) {
i := 2 * i;

} else {
i := 3 * i;

}

}
assert(i > 0);

}