procedure main() {
var nondet: bool;
var nondet_int: int;
var n: int;
var i: int;
var k: int;
var j: int;
havoc nondet_int;
n := nondet_int;
if(n < 1) {
return;
}
if(k < n) {
return;
}
j := 0;
while(j <= n - 1)
// insert invariants 
{
j := j + 1;
k := k - 1;

}
if(j < n) {
return;
}
assert(!(k <= -1));

}
