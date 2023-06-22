procedure main() {
var nondet: bool;
var nondet_int: int;
var x: int;
var y: int;
var k: int;
var j: int;
var i: int;
var n: int;
var m: int;
m := 0;
if((x + y) != k) {
return;
}
j := 0;
while(j <= n - 1)
// insert invariants 
invariant j >= 0;
invariant j <= n;
invariant m >= 0;
invariant m <= j;
{
if(j == i) {
x := x + 1;
y := y - 1;

} else {
y := y + 1;
x := x - 1;

}
havoc nondet;
if(nondet) {
m := j;
}
j := j + 1;

}
if(j < n) {
return;
}
assert(!(x + y <= k - 1 || x + y >= k + 1 || (n >= 1 && ((m <= -1) || (m >= n)))));

}