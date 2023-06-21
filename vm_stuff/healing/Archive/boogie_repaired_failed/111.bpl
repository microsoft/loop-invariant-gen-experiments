procedure main() {
var nondet: bool;
var i: int;
var n: int;
var sn: int;
sn := 0;
i := 1;
while(i <= n)
invariant i >= 1;
invariant i >= 2 ==> sn == ((i - 1) * (i - 2)) div 2;
invariant i > n ==> sn == (n * (n + 1)) div 2;
invariant sn >= 0 && sn <= (n * (n + 1)) div 2;
invariant sn == (i * (i - 1)) div 2;
{
i := i + 1;
sn := sn + 1;
}
if(sn != 0) {
assert(sn == n);
}
}