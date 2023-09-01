// SMACK-PRELUDE-BEGIN
procedure boogie_si_record_int(i: int);

function {:existential true} b0(i:int, j:int): bool;

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
const unique main: int;
axiom (main == -1024);
const unique __VERIFIER_assert: int;
axiom (__VERIFIER_assert == -2048);

procedure main() 
  modifies alloc, $CurrAddr;
{
  var $p: int;
  var $p1: int;
  var $b: bool;
  var $b2: bool;
  var $p3: int;
  var $p4: int;
  var $p5: int;
  var $p6: int;
$bb0:
  assume {:sourceloc "cggmp2005_true-unreach-call.c", 9, 0} true;
  // WARNING: ignoring llvm.debug call.
  assume true;
  assume {:sourceloc "cggmp2005_true-unreach-call.c", 10, 0} true;
  // WARNING: ignoring llvm.debug call.
  assume true;
  assume {:sourceloc "cggmp2005_true-unreach-call.c", 11, 0} true;
  $p := 10;
  $p1 := 1;
  goto $bb1;
$bb1:
  assert b0($p1, $p);

  assume {:sourceloc "cggmp2005_true-unreach-call.c", 11, 0} true;
  $b := $sge($p, $p1);
  assume {:sourceloc "cggmp2005_true-unreach-call.c", 11, 0} true;
  goto $bb4, $bb5;
$bb2:
  assume {:sourceloc "cggmp2005_true-unreach-call.c", 12, 0} true;
  $p5 := $add($p1, 2);
  assume {:sourceloc "cggmp2005_true-unreach-call.c", 12, 0} true;
  // WARNING: ignoring llvm.debug call.
  assume true;
  assume {:sourceloc "cggmp2005_true-unreach-call.c", 13, 0} true;
  $p6 := $add(-1, $p);
  assume {:sourceloc "cggmp2005_true-unreach-call.c", 13, 0} true;
  // WARNING: ignoring llvm.debug call.
  assume true;
  assume {:sourceloc "cggmp2005_true-unreach-call.c", 14, 0} true;
  $p := $p6;
  $p1 := $p5;
  goto $bb1;
$bb3:
  assume {:sourceloc "cggmp2005_true-unreach-call.c", 15, 0} true;
  $b2 := ($p == 6);
  assume {:sourceloc "cggmp2005_true-unreach-call.c", 15, 0} true;
  assert $b2;
  assume {:sourceloc "cggmp2005_true-unreach-call.c", 16, 0} true;
  return;
$bb4:
  assume {:sourceloc "cggmp2005_true-unreach-call.c", 11, 0} true;
  assume $b;
  goto $bb2;
$bb5:
  assume {:sourceloc "cggmp2005_true-unreach-call.c", 11, 0} true;
  assume !($b);
  goto $bb3;
}

procedure __VERIFIER_assert#1(p0: int) 
  returns ($r: int) ;
  modifies alloc, $CurrAddr;

// END SMACK-GENERATED CODE
