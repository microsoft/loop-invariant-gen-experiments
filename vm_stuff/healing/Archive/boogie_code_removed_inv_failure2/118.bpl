procedure main() {
var nondet: bool;
var i: int;
var size: int;
var sn: int;
sn := 0;
i := 1;
while(i <= size)
// Updated invariants
invariant i >= 1;
invariant sn >= 0;
invariant (size == 0) || (i > 1) ==> (sn == (i - 1) * i / 2);
{
i := i + 1;
sn := sn + 1;
}
if(sn != size) {
assert(sn == 0);
}
}