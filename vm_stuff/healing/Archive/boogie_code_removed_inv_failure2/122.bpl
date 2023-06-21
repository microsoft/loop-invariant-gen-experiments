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
// fixed invariants
invariant i >= 1;
invariant i <= size + (size > 0 ? 1 : 0);
invariant sn >= 0;
invariant sn <= (size * (size + 1)) / 2;
invariant (i > 1) ==> (size > 0) ==> (sn == (i * (i - 1)) / 2);
invariant (size == 0) || (i == 1) ==> (sn == 0);
{
i := i + 1;
sn := sn + 1;
}
if(sn != size) {
assert(sn == 0);
}
}