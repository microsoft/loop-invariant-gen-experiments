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
// fixed invariants
invariant (i >= 1) && (i <= n + 1);
invariant (n > 0) ==> (i > 1) ==> (sn == ((i - 1) * (i - 2)) / 2);
invariant (sn >= 0) && (sn <= n * (n + 1) / 2);
invariant (n == 0) ==> (sn == 0);
{
i := i + 1;
sn := sn + 1;
}
if(sn != 0) {
assert(sn == n);
}
}