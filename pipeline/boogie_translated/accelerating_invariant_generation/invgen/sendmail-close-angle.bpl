procedure main() {
var nondet: bool;
var nondet_int: int;
var in: int;
var inlen: int;
var bufferlen: int;
var buf: int;
var buflim: int;
if(!(bufferlen > 1)) {
return;

}
if(!(inlen > 0)) {
return;

}
if(!(bufferlen < inlen)) {
return;

}
buf := 0;
in := 0;
buflim := bufferlen - 2;
havoc nondet;
while(nondet)
// insert invariants 
{
if(buf == buflim) {
break;

}
assert(0 <= buf);
assert(buf < bufferlen);
buf := buf + 1;
in := in + 1;
assert(0 <= in);
assert(in < inlen);

havoc nondet;
//This comment is for codegen to add havoc nondet
}
assert(0 <= buf);
assert(buf < bufferlen);
buf := buf + 1;
assert(0 <= buf);
assert(buf < bufferlen);
buf := buf + 1;

}
