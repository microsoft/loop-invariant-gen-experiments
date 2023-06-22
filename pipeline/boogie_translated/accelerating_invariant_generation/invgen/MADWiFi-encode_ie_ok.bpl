procedure main() {
var nondet: bool;
var nondet_int: int;
var p: int;
var i: int;
var leader_len: int;
var bufsize: int;
var bufsize_0: int;
var ielen: int;
if(!(leader_len > 0)) {
return;

}
if(!(bufsize > 0)) {
return;

}
if(!(ielen > 0)) {
return;

}
if(bufsize < leader_len) {
return;

}
p := 0;
bufsize_0 := bufsize;
bufsize := bufsize - leader_len;
p := p + leader_len;
if(bufsize < 2 * ielen) {
return;

}
i := 0;
while((i < ielen) && (bufsize > 2))
// insert invariants 
{
assert(0 <= p);
assert(p + 1 < bufsize_0);
p := p + 2;
i := i + 1;

}

}
