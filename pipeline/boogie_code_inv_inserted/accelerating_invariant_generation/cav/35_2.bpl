procedure main() {
var nondet: bool;
var nondet_int: int;
var n: int;
var x: int;
x := 0;
while(x <= n - 1)
// insert invariants 
invariant x >= 0;
invariant x = 0 || x = 1 || x = 2 || x >= n;
{
x := x + 1;

}
if(x < n) {
return;
}
assert(!(n >= 1 && (x <= n - 1 || x >= n + 1)));

}