procedure main() {
var nondet: bool;
var nondet_int: int;
var i: int;
var j: int;
var n: int;
var sn: int;
j := 10;
havoc nondet_int;
n := nondet_int;
assume(n >= 0);
sn := 0;
i := 1;
while(i <= n)
// insert invariants 
{
if(i < j) {
sn := sn + 2;
}
j := j - 1;
i := i + 1;

}
assert(sn == n * 2 || sn == 0);

}
