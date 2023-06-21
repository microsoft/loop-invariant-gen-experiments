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
invariant sn == i - 1;
invariant sn > size ==> i == 1 && sn == 0;
{
i := i + 1;
sn := sn + 1;
}
if(sn != 0) {
assert(sn == size);
}
}