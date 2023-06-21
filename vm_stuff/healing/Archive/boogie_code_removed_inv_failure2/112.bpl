procedure main() {
var nondet: bool;
var i: int;
var n: int;
var sn: int;
var v1: int;
var v2: int;
var v3: int;
sn := 0;
i := 1;
while(i <= n)
// updated invariants
invariant i >= 1;
invariant sn >= 0;
invariant sn == (i-1) * i / 2;
invariant (i > n) ==> (sn == n * (n + 1) / 2);
{
i := i + 1;
sn := sn + 1;
}
if(sn != n) {
assert(sn == 0);
}
}