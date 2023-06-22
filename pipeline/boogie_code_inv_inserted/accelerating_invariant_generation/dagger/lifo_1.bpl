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
invariant I >= 0;
invariant Sa >= 0;
invariant Ea >= 0;
invariant Ma >= 0;
invariant Sb >= 0;
invariant Eb >= 0;
invariant Mb >= 0;
{
havoc nondet;
if(nondet) {
if(!(Sb >= 1)) {
return;
}
Sb := Sb - 1;
Sa := Ea + Ma + 1;
Ea := 0;
Ma := 0;

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
if(!(Ea >= 1)) {
return;
}
Ea := Ea - 1;
Ma := Ma + 1;

} else {
if(!(Eb >= 1)) {
return;
}
Eb := Eb - 1;
Mb := Mb + 1;

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
assert(Mb >= 0);
assert(Eb >= 0);
assert(Ma >= 0);
assert(Ea >= 0);

}