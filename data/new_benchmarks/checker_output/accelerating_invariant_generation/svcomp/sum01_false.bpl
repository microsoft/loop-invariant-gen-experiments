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
{
if(i < 10) {
sn := sn + 2;
}
i := i + 1;

}
assert(sn == n * 2 || sn == 0);

}