procedure main() {
var nondet: bool;
var i: int;
var n: int;
var sn: int;
sn := 0;
i := 1;
while(i <= n)
// insert invariants 
invariant sn == i - 1;
invariant i <= n + 1;
{
i := i + 1;
sn := sn + 1;
}
if(sn != n) {
assert(sn == 0);
}
}