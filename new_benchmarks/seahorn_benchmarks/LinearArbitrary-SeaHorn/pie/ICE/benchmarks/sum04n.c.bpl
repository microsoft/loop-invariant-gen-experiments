// SMACK-PRELUDE-BEGIN
function {:existential true} b0(i:int, sn:int, size: int): bool;
procedure boogie_si_record_int(i: int);

// Integer arithmetic
function $add(p1:int, p2:int) returns (int) {p1 + p2}
function $sub(p1:int, p2:int) returns (int) {p1 - p2}
function $mul(p1:int, p2:int) returns (int) {p1 * p2}
function $sdiv(p1:int, p2:int) returns (int);
function $udiv(p1:int, p2:int) returns (int);
function $srem(p1:int, p2:int) returns (int);
function $urem(p1:int, p2:int) returns (int);
function $and(p1:int, p2:int) returns (int);
axiom $and(0,0) == 0;
axiom $and(0,1) == 0;
axiom $and(1,0) == 0;
axiom $and(1,1) == 1;
function $or(p1:int, p2:int) returns (int);
axiom $or(0,0) == 0;
axiom $or(0,1) == 1;
axiom $or(1,0) == 1;
axiom $or(1,1) == 1;
function $xor(p1:int, p2:int) returns (int);
axiom $xor(0,0) == 0;
axiom $xor(0,1) == 1;
axiom $xor(1,0) == 1;
axiom $xor(1,1) == 0;
function $lshr(p1:int, p2:int) returns (int);
function $ashr(p1:int, p2:int) returns (int);
function $shl(p1:int, p2:int) returns (int);
function $ult(p1:int, p2:int) returns (bool) {p1 < p2}
function $ugt(p1:int, p2:int) returns (bool) {p1 > p2}
function $ule(p1:int, p2:int) returns (bool) {p1 <= p2}
function $uge(p1:int, p2:int) returns (bool) {p1 >= p2}
function $slt(p1:int, p2:int) returns (bool) {p1 < p2}
function $sgt(p1:int, p2:int) returns (bool) {p1 > p2}
function $sle(p1:int, p2:int) returns (bool) {p1 <= p2}
function $sge(p1:int, p2:int) returns (bool) {p1 >= p2}
function $nand(p1:int, p2:int) returns (int);
function $max(p1:int, p2:int) returns (int);
function $min(p1:int, p2:int) returns (int);
function $umax(p1:int, p2:int) returns (int);
function $umin(p1:int, p2:int) returns (int);
function $i2b(i: int) returns (bool);
axiom (forall i:int :: $i2b(i) <==> i != 0);
axiom $i2b(0) == false;
function $b2i(b: bool) returns (int);
axiom $b2i(true) == 1;
axiom $b2i(false) == 0;

// Floating point
type float;
function $fp(a:int) returns (float);
const $ffalse: float;
const $ftrue: float;
function $fadd(f1:float, f2:float) returns (float);
function $fsub(f1:float, f2:float) returns (float);
function $fmul(f1:float, f2:float) returns (float);
function $fdiv(f1:float, f2:float) returns (float);
function $frem(f1:float, f2:float) returns (float);
function $foeq(f1:float, f2:float) returns (bool);
function $foge(f1:float, f2:float) returns (bool);
function $fogt(f1:float, f2:float) returns (bool);
function $fole(f1:float, f2:float) returns (bool);
function $folt(f1:float, f2:float) returns (bool);
function $fone(f1:float, f2:float) returns (bool);
function $ford(f1:float, f2:float) returns (bool);
function $fueq(f1:float, f2:float) returns (bool);
function $fuge(f1:float, f2:float) returns (bool);
function $fugt(f1:float, f2:float) returns (bool);
function $fule(f1:float, f2:float) returns (bool);
function $fult(f1:float, f2:float) returns (bool);
function $fune(f1:float, f2:float) returns (bool);
function $funo(f1:float, f2:float) returns (bool);
function $fp2si(f:float) returns (int);
function $fp2ui(f:float) returns (int);
function $si2fp(i:int) returns (float);
function $ui2fp(i:int) returns (float);

// Memory region declarations: 0

// SMACK Flat Memory Model

function $ptr(obj:int, off:int) returns (int) {obj + off}
function $size(int) returns (int);
function $obj(int) returns (int);
function $off(ptr:int) returns (int) {ptr}

var alloc: [int] bool;
var $CurrAddr:int;

const unique $NULL: int;
axiom $NULL == 0;
const $UNDEF: int;

function $pa(pointer: int, index: int, size: int) returns (int);
function $trunc(p: int) returns (int);
function $p2i(p: int) returns (int);
function $i2p(p: int) returns (int);
function $p2b(p: int) returns (bool);
function $b2p(b: bool) returns (int);

axiom (forall p:int, i:int, s:int :: {$pa(p,i,s)} $pa(p,i,s) == p + i * s);
axiom (forall p:int :: $trunc(p) == p);

axiom $b2p(true) == 1;
axiom $b2p(false) == 0;
axiom (forall i:int :: $p2b(i) <==> i != 0);
axiom $p2b(0) == false;
axiom (forall i:int :: $p2i(i) == i);
axiom (forall i:int :: $i2p(i) == i);
procedure __SMACK_nondet() returns (p: int);
procedure __SMACK_nondetInt() returns (p: int);

procedure $malloc(obj_size: int) returns (new: int);
modifies $CurrAddr, alloc;
requires obj_size > 0;
ensures 0 < old($CurrAddr);
ensures new == old($CurrAddr);
ensures $CurrAddr > old($CurrAddr) + obj_size;
ensures $size(new) == obj_size;
ensures (forall x:int :: new <= x && x < new + obj_size ==> $obj(x) == new);
ensures alloc[new];
ensures (forall x:int :: {alloc[x]} x == new || old(alloc)[x] == alloc[x]);

procedure $free(pointer: int);
modifies alloc;
requires alloc[pointer];
requires $obj(pointer) == pointer;
ensures !alloc[pointer];
ensures (forall x:int :: {alloc[x]} x == pointer || old(alloc)[x] == alloc[x]);

procedure $alloca(obj_size: int) returns (new: int);
modifies $CurrAddr, alloc;
requires obj_size > 0;
ensures 0 < old($CurrAddr);
ensures new == old($CurrAddr);
ensures $CurrAddr > old($CurrAddr) + obj_size;
ensures $size(new) == obj_size;
ensures (forall x:int :: new <= x && x < new + obj_size ==> $obj(x) == new);
ensures alloc[new];
ensures (forall x:int :: {alloc[x]} x == new || old(alloc)[x] == alloc[x]);

// SMACK-PRELUDE-END
// BEGIN SMACK-GENERATED CODE
const unique __VERIFIER_assert: int;
axiom (__VERIFIER_assert == -1024);
const unique main: int;
axiom (main == -2048);
const unique __VERIFIER_nondet_int: int;
axiom (__VERIFIER_nondet_int == -3072);

procedure __VERIFIER_assert(cond: int) 
  modifies alloc, $CurrAddr;
{
  var $b: bool;
$bb0:
  assume {:sourceloc "sum04_gen.c", 1, 0} true;
  // WARNING: ignoring llvm.debug call.
  assume true;
  assume {:sourceloc "sum04_gen.c", 2, 0} true;
  $b := (cond != 0);
  assume {:sourceloc "sum04_gen.c", 2, 0} true;
  goto $bb3, $bb4;
$bb1:
  assume {:sourceloc "sum04_gen.c", 5, 0} true;
  return;
$bb2:
  assume {:sourceloc "sum04_gen.c", 2, 0} true;
  goto $bb5;
$bb3:
  assume {:sourceloc "sum04_gen.c", 2, 0} true;
  assume $b;
  goto $bb1;
$bb4:
  assume {:sourceloc "sum04_gen.c", 2, 0} true;
  assume !($b);
  goto $bb2;
$bb5:
  assume {:sourceloc "sum04_gen.c", 3, 0} true;
  goto $bb5;
}

procedure main() 
  returns ($r: int) 
  modifies alloc, $CurrAddr;
{
  var $p: int;
  var $p1: int;
  var $p2: int;
  var $b: bool;
  var $p3: int;
  var $b4: bool;
  var $b5: bool;
  var $b6: bool;
  var $p7: int;
  var $p8: int;
  var $p9: int;
$bb0:
  assume {:sourceloc "sum04_gen.c", 11, 0} true;
  // WARNING: ignoring llvm.debug call.
  assume true;
  assume {:sourceloc "sum04_gen.c", 12, 0} true;
  havoc $p;
  assume {:sourceloc "sum04_gen.c", 12, 0} true;
  // WARNING: ignoring llvm.debug call.
  assume true;
  assume {:sourceloc "sum04_gen.c", 13, 0} true;
  // WARNING: ignoring llvm.debug call.
  assume true;
  assume {:sourceloc "sum04_gen.c", 13, 0} true;
  $p1 := 1;
  $p2 := 0;
  goto $bb1;
$bb1:
  assert b0($p1,$p2, $p);
  // assert 0 <= $p2 && $p2 == $p1 - 1 && ($p1 <= $p + 1 || ($p2 == 0 && $p1 == 1));

  assume {:sourceloc "sum04_gen.c", 13, 0} true;
  $b := $sle($p1, $p);
  assume {:sourceloc "sum04_gen.c", 13, 0} true;
  goto $bb4, $bb5;
$bb2:
  assume {:sourceloc "sum04_gen.c", 14, 0} true;
  $p8 := $add($p2, 1);
  assume {:sourceloc "sum04_gen.c", 14, 0} true;
  // WARNING: ignoring llvm.debug call.
  assume true;
  assume {:sourceloc "sum04_gen.c", 15, 0} true;
  goto $bb10;
$bb3:
  assume {:sourceloc "sum04_gen.c", 16, 0} true;
  $p3 := $mul($p, 1);
  assume {:sourceloc "sum04_gen.c", 16, 0} true;
  $b4 := ($p2 == $p3);
  assume {:sourceloc "sum04_gen.c", 16, 0} true;
  $b5 := true;
  goto $bb8, $bb9;
$bb4:
  assume {:sourceloc "sum04_gen.c", 13, 0} true;
  assume $b;
  goto $bb2;
$bb5:
  assume {:sourceloc "sum04_gen.c", 13, 0} true;
  assume !($b);
  goto $bb3;
$bb6:
  assume {:sourceloc "sum04_gen.c", 16, 0} true;
  $p7 := $b2p($b5);
  assume {:sourceloc "sum04_gen.c", 16, 0} true;
  assert $p7 == 1;
  assume {:sourceloc "sum04_gen.c", 17, 0} true;
  $r := 0;
  return;
$bb7:
  assume {:sourceloc "sum04_gen.c", 16, 0} true;
  $b6 := ($p2 == 0);
  assume {:sourceloc "sum04_gen.c", 16, 0} true;
  $b5 := $b6;
  goto $bb6;
$bb8:
  assume {:sourceloc "sum04_gen.c", 16, 0} true;
  assume $b4;
  goto $bb6;
$bb9:
  assume {:sourceloc "sum04_gen.c", 16, 0} true;
  assume !($b4);
  goto $bb7;
$bb10:
  assume {:sourceloc "sum04_gen.c", 13, 0} true;
  $p9 := $add($p1, 1);
  assume {:sourceloc "sum04_gen.c", 13, 0} true;
  // WARNING: ignoring llvm.debug call.
  assume true;
  assume {:sourceloc "sum04_gen.c", 13, 0} true;
  $p1 := $p9;
  $p2 := $p8;
  goto $bb1;
}

procedure __VERIFIER_nondet_int() 
  returns ($r: int) ;
  modifies alloc, $CurrAddr;

// END SMACK-GENERATED CODE
