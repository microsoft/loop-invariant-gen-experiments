procedure main() {
var nondet: bool;
var nondet_int: int;
var sn: int;
var loop1: int;
var n1: int;
var x: int;
sn := 0;
havoc nondet_int;
loop1 := nondet_int;
assume(loop1 >= 0);
havoc nondet_int;
n1 := nondet_int;
assume(n1 >= 0);
x := 0;
while(true)
invariant x >= 0;
invariant x <= 10;
invariant sn >= 0;
invariant x <= 10 ==> (sn == x * 2);
{
if(x < 10) {
sn := sn + 2;
}
x := x + 1;
assert(sn == x * 2 || sn == 0);

}

}