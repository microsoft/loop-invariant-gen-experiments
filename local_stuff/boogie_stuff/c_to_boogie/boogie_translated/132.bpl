procedure main() {
var nondet: bool;
var i: int;
var j: int;
var c: int;
var t: int;
i := 0;
havoc nondet;
while(nondet)
// insert invariants 
invariant i >= 0;
{
    havoc nondet;
if(c > 48) {
if(c < 57) {
j := i + i;
t := c - 48;
i := j + t;
}
}
}
assert(i >= 0);
}