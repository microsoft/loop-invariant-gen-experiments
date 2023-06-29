procedure main() {
var nondet: bool;
var c: int;
c := 0;
havoc nondet;
while(nondet)
// insert invariants 
{
havoc nondet;
if(nondet) {
if(c != 40) {
c := c + 1;
}
} else {
if(c == 40) {
c := 1;
}
}
}
if(c != 40) {
assert(c <= 40);
}
}