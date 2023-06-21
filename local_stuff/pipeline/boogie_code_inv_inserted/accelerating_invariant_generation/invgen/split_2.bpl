procedure main() {
var nondet: bool;
var nondet_int: int;
var k: int;
var b: bool;
var i: int;
var j: int;
var n: int;
k := 100;
i := j;
n := 0;
while(n < 2 * k)
// insert invariants 
invariant (n % 2 == 0) ==> (b == (old(b)));
invariant (n % 2 == 1) ==> (b != (old(b)));
invariant n >= 0;
invariant n <= 2 * k;
{
if(b) {
i := i + 1;

} else {
j := j + 1;

}
b := !b;
n := n + 1;

}
assert(i == j);

}