procedure main() {
var nondet: bool;
var i: int;
var n: int;
var sn: int;
sn := 0;
i := 1;
while(i <= n)
invariant i >= 1;
invariant (i > 1) ==> (sn == ((i - 1) * i) / 2);
invariant sn == (i * (i - 1)) / 2;
invariant 1 <= i && i <= n + 1;
invariant sn >= 0 && sn <= n * (n + 1) / 2;
{
i := i + 1;
sn := sn + 1;
}
if(sn != 0) {
assert(sn == n);
}
}