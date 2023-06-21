procedure main() {
var nondet: bool;
var nondet_int: int;
var barber: int;
var chair: int;
var open: int;
var p1: int;
var p2: int;
var p3: int;
var p4: int;
var p5: int;
barber := 0;
chair := 0;
open := 0;
p1 := 0;
p2 := 0;
p3 := 0;
p4 := 0;
p5 := 0;
havoc nondet;
while(nondet)
// insert invariants 
invariant barber >= 0;
invariant chair >= 0;
invariant open >= 0;
invariant 0 <= p1 && p1 <= 1;
invariant 0 <= p2 && p2 <= 1;
invariant 0 <= p3 && p3 <= 1;
invariant 0 <= p4 && p4 <= 1;
invariant 0 <= p5 && p5 <= 3;
{
havoc nondet;
if(nondet) {
if(!(p1 >= 0)) {
return;
}
if(!(p1 <= 0)) {
return;
}
if(!(barber >= 1)) {
return;
}
barber := barber - 1;
chair := chair + 1;
p1 := 1;

} else {
havoc nondet;
if(nondet) {
if(!(p2 >= 0)) {
return;
}
if(!(p2 <= 0)) {
return;
}
if(!(barber >= 1)) {
return;
}
barber := barber - 1;
chair := chair + 1;
p2 := 1;

} else {
havoc nondet;
if(nondet) {
if(!(p2 >= 1)) {
return;
}
if(!(p2 <= 1)) {
return;
}
if(!(open >= 1)) {
return;
}
open := open - 1;
p2 := 0;

} else {
havoc nondet;
if(nondet) {
if(!(p3 >= 0)) {
return;
}
if(!(p3 <= 0)) {
return;
}
if(!(barber >= 1)) {
return;
}
barber := barber - 1;
chair := chair + 1;
p3 := 1;

} else {
havoc nondet;
if(nondet) {
if(!(p3 >= 1)) {
return;
}
if(!(p3 <= 1)) {
return;
}
if(!(open >= 1)) {
return;
}
open := open - 1;
p3 := 0;

} else {
havoc nondet;
if(nondet) {
if(!(p4 >= 0)) {
return;
}
if(!(p4 <= 0)) {
return;
}
if(!(barber >= 1)) {
return;
}
barber := barber - 1;
chair := chair + 1;
p4 := p4 + 1;

} else {
havoc nondet;
if(nondet) {
if(!(p4 >= 1)) {
return;
}
if(!(p4 <= 1)) {
return;
}
if(!(open >= 1)) {
return;
}
open := open - 1;
p4 := p4 - 1;

} else {
havoc nondet;
if(nondet) {
if(!(p5 >= 0)) {
return;
}
if(!(p5 <= 0)) {
return;
}
barber := barber + 1;
p5 := 1;

} else {
havoc nondet;
if(nondet) {
if(!(p5 >= 1)) {
return;
}
if(!(p5 <= 1)) {
return;
}
if(!(chair >= 1)) {
return;
}
chair := chair - 1;
p5 := 2;

} else {
havoc nondet;
if(nondet) {
if(!(p5 >= 2)) {
return;
}
if(!(p5 <= 2)) {
return;
}
open := open + 1;
p5 := 3;

} else {
havoc nondet;
if(nondet) {
if(!(p5 >= 3)) {
return;
}
if(!(p5 <= 3)) {
return;
}
if(!(open == 0)) {
return;
}
p5 := 0;

} else {
if(!(p1 >= 1)) {
return;
}
if(!(p1 <= 1)) {
return;
}
if(!(open >= 1)) {
return;
}
open := open - 1;
p1 := 0;

}

}

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
assert(p5 <= 3);
assert(p5 >= open);

}