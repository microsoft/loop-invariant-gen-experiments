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
invariant i >= 1;
invariant (size > 0 && i >= 1) ==> (sn == ((i * (i - 1)) div 2) - 1);
invariant (i >= 1) ==> (i * i <= 2 * sn + 2 * i + 1);
invariant (sn >= 0) && (sn <= (size * (size + 1)) div 2);
{
i := i + 1;
sn := sn + 1;
}
if(sn != size) {
assert(sn == 0);
}
}