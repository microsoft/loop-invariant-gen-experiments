procedure main() {
var nondet: bool;
var i: int;
var n: int;
var sn: int;
sn := 0;
i := 1;
while(i <= n)
invariant i >= 1;
invariant i <= n + 2;
invariant sn == ((i - 1) * (i - 1)) div 2;
invariant sn <= n * (n + 1) div 2;
{
i := i + 1;
sn := sn + 1;
}
if(sn != n) {
assert(sn == 0);
}
}