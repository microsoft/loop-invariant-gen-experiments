procedure main() {
var nondet: bool;
var nondet_int: int;
var cp1_off: int;
var n1: int;
var n2: int;
var mc_i: int;
var MAXDATA: int;
if(!(MAXDATA > 0)) {
return;

}
if(!(n1 <= MAXDATA * 2)) {
return;

}
if(!(cp1_off <= n1)) {
return;

}
if(!(n2 <= MAXDATA * 2 - n1)) {
return;

}
mc_i := 0;
while(mc_i < n2)
// insert invariants 
{
assert(cp1_off + mc_i < MAXDATA * 2);
mc_i := mc_i + 1;

}

}
