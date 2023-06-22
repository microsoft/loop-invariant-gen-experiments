procedure main() {
var nondet: bool;
var i: int;
var size: int;
var sn: int;
sn := 0;
i := 1;
while(i <= size)
invariant i >= 1;
invariant sn >= 0;
invariant i > 1 ==> sn == (i * (i - 1)) div 2;
invariant i <= size + 1;
invariant sn * 2 <= i * (i - 1) || i == 1;
invariant i * (i - 1) <= 2 * sn;
invariant sn * 2 <= size * (size + 1);
{
i := i + 1;
sn := sn + 1;
}
if(sn != size) {
assert(sn == 0);
}
}