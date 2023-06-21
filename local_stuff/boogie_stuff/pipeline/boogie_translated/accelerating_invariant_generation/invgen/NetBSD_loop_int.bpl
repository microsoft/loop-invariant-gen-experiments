procedure main() {
var nondet: bool;
var nondet_int: int;
var MAXPATHLEN: int;
var buf_off: int;
var pattern_off: int;
var bound_off: int;
var glob3_pathbuf_off: int;
var glob3_pathend_off: int;
var glob3_pathlim_off: int;
var glob3_pattern_off: int;
var glob3_dc: int;
if(!(MAXPATHLEN > 0)) {
return;

}
buf_off := 0;
pattern_off := 0;
bound_off := 0 + (MAXPATHLEN + 1) - 1;
glob3_pathbuf_off := buf_off;
glob3_pathend_off := buf_off;
glob3_pathlim_off := bound_off;
glob3_pattern_off := pattern_off;
glob3_dc := 0;
while(true)
// insert invariants 
{
if(glob3_pathend_off + glob3_dc >= glob3_pathlim_off) {
break;

} else {
glob3_dc := glob3_dc + 1;
assert(0 <= glob3_dc);
assert(glob3_dc < MAXPATHLEN + 1);
havoc nondet;
if(nondet) {
return;

}

}

}

}
