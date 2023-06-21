procedure main() {
var nondet: bool;
var nondet_int: int;
var fbuflen: int;
var fb: int;
if(!(fbuflen > 0)) {
return;

}
fb := 0;
havoc nondet;
while(nondet)
// insert invariants 
invariant 0 <= fb;
invariant fb < fbuflen;
{
havoc nondet;
if(nondet) {
break;

}
havoc nondet;
if(nondet) {
break;

}
assert(0 <= fb);
assert(fb < fbuflen);
fb := fb + 1;
if(fb >= fbuflen - 1) {
fb := 0;

}
assert(0 <= fb);
assert(fb < fbuflen);
fb := fb + 1;
if(fb >= fbuflen - 1) {
fb := 0;

}
assert(0 <= fb);
assert(fb < fbuflen);
fb := fb + 1;
if(fb >= fbuflen - 1) {
fb := 0;

}

havoc nondet;
//This comment is for codegen to add havoc nondet
}
if(fb > 0) {
assert(0 <= fb);
assert(fb < fbuflen);

}

}