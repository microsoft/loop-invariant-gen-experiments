procedure main() {
var nondet: bool;
var nondet_int: int;
var n: int;
var i: int;
var j: int;
havoc nondet_int;
n := nondet_int;
i := 0;
j := 0;
if(!(n >= 0)) {
return;
}
while(i < n)
// insert invariants 
invariant i == j;
invariant i <= n;
{
i := i + 1;
j := j + 1;

}
assert(!(j >= n + 1));

}