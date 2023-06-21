procedure main() {
var nondet: bool;
var nondet_int: int;
var n: int;
var m: int;
var x: int;
var y: int;
x := 0;
havoc nondet_int;
n := nondet_int;
havoc nondet_int;
m := nondet_int;
y := m;
if(n < 0) {
return;
}
if(m < 0) {
return;
}
if(m > n - 1) {
return;
}
while(x <= n - 1)
// insert invariants 
{
x := x + 1;
if(x >= m + 1) {
y := y + 1;
} else {
if(x > m) {
return;
}
}
x := x;

}
if(x < n) {
return;
}
assert(!(y >= n + 1));

}
