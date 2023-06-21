procedure main() {
var nondet: bool;
var nondet_int: int;
var I: int;
var Sa: int;
var Ea: int;
var Ma: int;
var Sb: int;
var Eb: int;
var Mb: int;
if(!(I >= 1)) {
return;
}
Sa := 0;
Ea := 0;
Ma := 0;
Sb := 0;
Eb := 0;
Mb := 0;
havoc nondet;
while(nondet)
// insert invariants 
{
havoc nondet;
if(nondet) {
if(!(Eb >= 1)) {
return;
}
Eb := Eb - 1;
Mb := Mb + 1;

} else {
havoc nondet;
if(nondet) {
if(!(Ea >= 1)) {
return;
}
Ea := Ea - 1;
Ma := Ma + 1;

} else {
havoc nondet;
if(nondet) {
if(!(Sa >= 1)) {
return;
}
Sa := Sa - 1;
I := I + Sb + Eb + Mb;
Sb := 0;
Eb := 1;
Mb := 0;

} else {
havoc nondet;
if(nondet) {
if(!(Sb >= 1)) {
return;
}
I := I + Sb + Eb + Mb;
Sb := 0;
Eb := 1;
Mb := 0;

} else {
havoc nondet;
if(nondet) {
if(!(Sb >= 1)) {
return;
}
Sb := Sb - 1;
I := I + Sa + Ea + Ma;
Sa := 0;
Ea := 1;
Ma := 0;

} else {
havoc nondet;
if(nondet) {
if(!(Sa >= 1)) {
return;
}
I := I + Sa + Ea + Ma;
Sa := 0;
Ea := 1;
Ma := 0;

} else {
havoc nondet;
if(nondet) {
if(!(Sa >= 1)) {
return;
}
Sa := Sa - 1;
Sb := Sb + Eb + Mb + 1;
Eb := 0;
Mb := 0;

} else {
havoc nondet;
if(nondet) {
if(!(I >= 1)) {
return;
}
I := I - 1;
Sb := Sb + Eb + Mb + 1;
Eb := 0;
Mb := 0;

} else {
havoc nondet;
if(nondet) {
if(!(I >= 1)) {
return;
}
I := I - 1;
Sa := Sa + Ea + Ma + 1;
Ea := 0;
Ma := 0;

} else {
if(!(Sb >= 1)) {
return;
}
Sb := Sb - 1;
Sa := Ea + Ma + 1;
Ea := 0;
Ma := 0;

}

}

}

}

}

}

}

}

}

havoc nondet;
//This comment is for codegen to add havoc nondet
}
assert(Ea + Ma <= 1);
assert(Eb + Mb <= 1);
assert(I + Sa + Ea + Ma + Sb + Eb + Mb >= 1);

}
