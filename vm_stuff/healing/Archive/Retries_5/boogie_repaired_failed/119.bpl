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
invariant sn == (i * (i - 1)) / 2;
invariant i <= size + 1;
{
i := i + 1;
sn := sn + 1;
}
if(sn != 0) {
assert(sn == size);
}
}