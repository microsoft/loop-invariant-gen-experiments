procedure main() {
var nondet: bool;
var nondet_int: int;
var n: int;
var x: int;
x := 0;
while(x <= n - 1)
// insert invariants 
{
x := x + 1;

}
if(x < n) {
return;
}
assert(!(n >= 1 && (x <= n - 1 || x >= n + 1)));

}
