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
if(c != 4) {
c := c + 1;
}
} else {
if(c == 4) {
c := 1;
}
}
}
if(c < 0) {
if(c > 4) {
assert(c == 4);
}
}
}