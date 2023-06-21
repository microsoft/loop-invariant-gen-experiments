procedure main() {
var nondet: bool;
var nondet_int: int;
var idBitLength: int;
var material_length: int;
var nlen: int;
var j: int;
var k: int;
assume(nlen == idBitLength / 32);
j := 0;
while((j < idBitLength / 8) && (j < material_length))
// insert invariants 
{
assert(0 <= j);
assert(j < material_length);
assert(0 <= j / 4);
assert(j / 4 < nlen);
j := j + 1;

}

}
