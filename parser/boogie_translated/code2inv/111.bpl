procedure main() {
var nondet: bool;
var i: int;
var n: int;
var sn: int;
sn := 0;
i := 1;
while(i <= n)
// insert invariants 
{
i := i + 1;
sn := sn + 1;
}
if(sn != 0) {
assert(sn == n);
}
}