procedure main() {
var nondet: bool;
var i: int;
var n: int;
var sn: int;
var v1: int;
var v2: int;
var v3: int;
sn := 0;
i := 1;
while(i <= n)
// insert invariants 
invariant i >= 1;
invariant sn >= 0;
invariant sn == i * (i - 1) div 2;
{
i := i + 1;
sn := sn + 1;
}
if(sn != n) {
assert(sn == 0);
}
}