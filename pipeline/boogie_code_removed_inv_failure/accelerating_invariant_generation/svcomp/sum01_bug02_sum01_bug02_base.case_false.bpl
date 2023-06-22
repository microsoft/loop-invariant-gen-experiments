procedure main() {
var nondet: bool;
var nondet_int: int;
var i: int;
var n: int;
var sn: int;
havoc nondet_int;
n := nondet_int;
assume(n >= 0);
sn := 0;
i := 1;
while(i <= n)
// insert invariants 
invariant i >= 1;
invariant sn == (i - 1) * 2 || (sn == -10 && i == 5);
invariant i <= n + 1;
invariant i >= 1;
invariant sn == 2 * (i - 1) || (sn == -10 && i == 5);
invariant i <= n + 1;
invariant i >= 1;
invariant sn == 2 * (i - 1) || (sn == -10 && i == 5);
invariant i <= n + 1;
{
sn := sn + 2;
if(i == 4) {
sn := -10;
}
i := i + 1;

}
assert(sn == n * 2 || sn == 0);

}