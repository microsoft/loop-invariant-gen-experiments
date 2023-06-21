procedure main() {
var nondet: bool;
var nondet_int: int;
var x: int;
var m: int;
var n: int;
x := 0;
m := 0;
while(x < n)
// insert invariants 
{
havoc nondet;
if(nondet) {
m := x;
}
x := x + 1;

}
if(n > 0) {
assert(0 <= m);
assert(m < n);

}

}
