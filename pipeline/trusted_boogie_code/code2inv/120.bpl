procedure main() {
var nondet: bool;
var i: int;
var sn: int;
sn := 0;
i := 1;
while(i <= 8)
// insert invariants 
{
i := i + 1;
sn := sn + 1;
}
if(sn != 8) {
assert(sn == 0);
}
}