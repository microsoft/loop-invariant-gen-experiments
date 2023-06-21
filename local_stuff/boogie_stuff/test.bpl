procedure main() {
var nondet: bool;
var i: int;
var size: int;
var sn: int;
sn := 0;
i := 1;
while(i <= size)
invariant sn == i - 1;
// invariant size > 0 ==> i <= size + 1;
// invariant size <= 0 ==> (sn == 0);
// invariant i == 1 || i <= size + 1;
invariant sn == 0 || sn <= size;
{
i := i + 1;
sn := sn + 1;
}
if(sn != 0) {
assert(sn == size);
}
}