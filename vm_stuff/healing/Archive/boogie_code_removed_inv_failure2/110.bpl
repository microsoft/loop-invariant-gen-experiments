procedure main() {
var nondet: bool;
var i: int;
var n: int;
var sn: int;
sn := 0;
i := 1;
while(i <= n)
// Fixed and strengthened invariants
invariant (i <= n) ==> (i >= 1); // holds conditionally after loop entry
invariant (i >= 1) ==> (sn == (i - 1) * i / 2); // holds on loop entry and during the loop; fixed the formula
invariant sn + (n - i + 1) * (n - i + 2) / 2 == n * (n + 1) / 2; // new invariant tracking relationship between i, n, and sn
invariant i > n ==> sn == n * (n + 1) / 2; // additional invariant for i > n case
{
i := i + 1;
sn := sn + 1;
}
if(sn != n) {
assert(sn == 0);
}
}