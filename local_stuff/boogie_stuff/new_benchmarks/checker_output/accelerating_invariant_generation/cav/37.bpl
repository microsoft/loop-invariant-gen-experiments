procedure main() {
var nondet: bool;
var nondet_int: int;
var x: int;
var m: int;
var n: int;
x := 0;
m := 0;
havoc nondet_int;
n := nondet_int;
while(x <= n - 1)
// insert invariants 
{
havoc nondet;
if(nondet) {
m := x;

}
x := x + 1;

}
if(x < n) {
return;
}
assert(!(n >= 1 && (m <= -1 || m >= n)));

}
