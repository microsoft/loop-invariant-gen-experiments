procedure main() {
var nondet: bool;
var i: int;
var size: int;
var sn: int;
var v1: int;
var v2: int;
var v3: int;
sn := 0;
i := 1;
while(i <= size)
// insert invariants 
{
i := i + 1;
sn := sn + 1;
}
if(sn != size) {
assert(sn == 0);
}
}