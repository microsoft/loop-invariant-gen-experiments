procedure main() {
var nondet: bool;
var nondet_int: int;
var i: int;
var sn: int;
sn := 0;
i := 1;
while(i <= 8)
// insert invariants 
{
if(i < 4) {
sn := sn + 2;
}
i := i + 1;

}
assert(sn == 8 * 2 || sn == 0);

}
