procedure main() {
var nondet: bool;
var nondet_int: int;
var i: int;
var j: int;
var n: int;
var sn: int;
j := 10;
havoc nondet_int;
n := nondet_int;
assume(n >= 0);
sn := 0;
i := 1;
while(i <= n)
// insert invariants 
invariant i >= 1;
invariant i <= n + 1;
invariant j >= 0;
invariant n >= 0;
invariant sn >= 0;
invariant sn % 2 == 0;
{
if(i < j) {
sn := sn + 2;
}
j := j - 1;
i := i + 1;

}
assert(sn == n * 2 || sn == 0);

}