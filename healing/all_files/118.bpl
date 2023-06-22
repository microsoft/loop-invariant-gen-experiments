procedure main() {
var nondet: bool;
var i: int;
var size: int;
var sn: int;
sn := 0;
i := 1;
while(i <= size)
// insert invariants 
invariant sn == (i - 1);
invariant sn == (i - 1);
invariant sn == (i - 1);
{
i := i + 1;
sn := sn + 1;
}
if(sn != size) {
assert(sn == 0);
}
}