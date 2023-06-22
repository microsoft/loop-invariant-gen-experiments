procedure main() {
var nondet: bool;
var nondet_int: int;
var invalid: int;
var unowned: int;
var nonexclusive: int;
var exclusive: int;
if(!(exclusive == 0)) {
return;
}
if(!(nonexclusive == 0)) {
return;
}
if(!(unowned == 0)) {
return;
}
if(!(invalid >= 1)) {
return;
}
havoc nondet;
while(nondet)
// insert invariants 
{
havoc nondet;
if(nondet) {
if(!(invalid >= 1)) {
return;
}
nonexclusive := nonexclusive + exclusive;
exclusive := 0;
invalid := invalid - 1;
unowned := unowned + 1;

} else {
havoc nondet;
if(nondet) {
if(!(nonexclusive + unowned >= 1)) {
return;
}
invalid := invalid + unowned + nonexclusive - 1;
exclusive := exclusive + 1;
unowned := 0;
nonexclusive := 0;

} else {
if(!(invalid >= 1)) {
return;
}
unowned := 0;
nonexclusive := 0;
exclusive := 1;
invalid := invalid + unowned + exclusive + nonexclusive - 1;

}

}

havoc nondet;
//This comment is for codegen to add havoc nondet
}
assert(exclusive >= 0);
assert(unowned >= 0);
assert(invalid + unowned + exclusive + nonexclusive >= 1);

}
