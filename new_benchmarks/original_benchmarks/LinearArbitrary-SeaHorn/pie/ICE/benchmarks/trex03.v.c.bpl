procedure boogie_si_record_int(i: int);

function {:existential true} b0(x1:int,x2:int,x3:int, v1: int, v2: int, v3: int): bool;


function $add(p1: int, p2: int) : int;

axiom (forall p1: int, p2: int :: { $add(p1, p2): int } $add(p1, p2): int == p1 + p2);

function $sub(p1: int, p2: int) : int;

axiom (forall p1: int, p2: int :: { $sub(p1, p2): int } $sub(p1, p2): int == p1 - p2);

function $mul(p1: int, p2: int) : int;

axiom (forall p1: int, p2: int :: { $mul(p1, p2): int } $mul(p1, p2): int == p1 * p2);

function $sdiv(p1: int, p2: int) : int;

function $udiv(p1: int, p2: int) : int;

function $srem(p1: int, p2: int) : int;

function $urem(p1: int, p2: int) : int;

function $and(p1: int, p2: int) : int;

axiom $and(0, 0) == 0;

axiom $and(0, 1) == 0;

axiom $and(1, 0) == 0;

axiom $and(1, 1) == 1;

function $or(p1: int, p2: int) : int;

axiom $or(0, 0) == 0;

axiom $or(0, 1) == 1;

axiom $or(1, 0) == 1;

axiom $or(1, 1) == 1;

function $xor(p1: int, p2: int) : int;

axiom $xor(0, 0) == 0;

axiom $xor(0, 1) == 1;

axiom $xor(1, 0) == 1;

axiom $xor(1, 1) == 0;

function $lshr(p1: int, p2: int) : int;

function $ashr(p1: int, p2: int) : int;

function $shl(p1: int, p2: int) : int;

function $ult(p1: int, p2: int) : bool;

axiom (forall p1: int, p2: int :: { $ult(p1, p2): bool } $ult(p1, p2): bool == (p1 < p2));

function $ugt(p1: int, p2: int) : bool;

axiom (forall p1: int, p2: int :: { $ugt(p1, p2): bool } $ugt(p1, p2): bool == (p1 > p2));

function $ule(p1: int, p2: int) : bool;

axiom (forall p1: int, p2: int :: { $ule(p1, p2): bool } $ule(p1, p2): bool == (p1 <= p2));

function $uge(p1: int, p2: int) : bool;

axiom (forall p1: int, p2: int :: { $uge(p1, p2): bool } $uge(p1, p2): bool == (p1 >= p2));

function $slt(p1: int, p2: int) : bool;

axiom (forall p1: int, p2: int :: { $slt(p1, p2): bool } $slt(p1, p2): bool == (p1 < p2));

function $sgt(p1: int, p2: int) : bool;

axiom (forall p1: int, p2: int :: { $sgt(p1, p2): bool } $sgt(p1, p2): bool == (p1 > p2));

function $sle(p1: int, p2: int) : bool;

axiom (forall p1: int, p2: int :: { $sle(p1, p2): bool } $sle(p1, p2): bool == (p1 <= p2));

function $sge(p1: int, p2: int) : bool;

axiom (forall p1: int, p2: int :: { $sge(p1, p2): bool } $sge(p1, p2): bool == (p1 >= p2));

function $nand(p1: int, p2: int) : int;

function $max(p1: int, p2: int) : int;

function $min(p1: int, p2: int) : int;

function $umax(p1: int, p2: int) : int;

function $umin(p1: int, p2: int) : int;

function $i2b(i: int) : bool;

axiom (forall i: int :: $i2b(i) <==> i != 0);

axiom $i2b(0) == false;

function $b2i(b: bool) : int;

axiom $b2i(true) == 1;

axiom $b2i(false) == 0;

type float;

function $fp(a: int) : float;

const $ffalse: float;

const $ftrue: float;

function $fadd(f1: float, f2: float) : float;

function $fsub(f1: float, f2: float) : float;

function $fmul(f1: float, f2: float) : float;

function $fdiv(f1: float, f2: float) : float;

function $frem(f1: float, f2: float) : float;

function $foeq(f1: float, f2: float) : bool;

function $foge(f1: float, f2: float) : bool;

function $fogt(f1: float, f2: float) : bool;

function $fole(f1: float, f2: float) : bool;

function $folt(f1: float, f2: float) : bool;

function $fone(f1: float, f2: float) : bool;

function $ford(f1: float, f2: float) : bool;

function $fueq(f1: float, f2: float) : bool;

function $fuge(f1: float, f2: float) : bool;

function $fugt(f1: float, f2: float) : bool;

function $fule(f1: float, f2: float) : bool;

function $fult(f1: float, f2: float) : bool;

function $fune(f1: float, f2: float) : bool;

function $funo(f1: float, f2: float) : bool;

function $fp2si(f: float) : int;

function $fp2ui(f: float) : int;

function $si2fp(i: int) : float;

function $ui2fp(i: int) : float;

function $ptr(obj: int, off: int) : int;

axiom (forall obj: int, off: int :: { $ptr(obj, off): int } $ptr(obj, off): int == obj + off);

function $size(int) : int;

function $obj(int) : int;

function $off(ptr: int) : int;

axiom (forall ptr: int :: { $off(ptr): int } $off(ptr): int == ptr);

var alloc: [int]bool;

var $CurrAddr: int;

const unique $NULL: int;

const $UNDEF: int;

function $pa(pointer: int, index: int, size: int) : int;

function $trunc(p: int) : int;

function $p2i(p: int) : int;

function $i2p(p: int) : int;

function $p2b(p: int) : bool;

function $b2p(b: bool) : int;

axiom (forall p: int, i: int, s: int :: { $pa(p, i, s) } $pa(p, i, s) == p + i * s);

axiom (forall p: int :: $trunc(p) == p);

axiom $b2p(true) == 1;

axiom $b2p(false) == 0;

axiom (forall i: int :: $p2b(i) <==> i != 0);

axiom $p2b(0) == false;

axiom (forall i: int :: $p2i(i) == i);

axiom (forall i: int :: $i2p(i) == i);

procedure __SMACK_nondet() returns (p: int);



procedure __SMACK_nondetInt() returns (p: int);



procedure $malloc(obj_size: int) returns (new: int);
  requires obj_size > 0;
  modifies $CurrAddr, alloc;
  ensures 0 < old($CurrAddr);
  ensures new == old($CurrAddr);
  ensures $CurrAddr > old($CurrAddr) + obj_size;
  ensures $size(new) == obj_size;
  ensures (forall x: int :: new <= x && x < new + obj_size ==> $obj(x) == new);
  ensures alloc[new];
  ensures (forall x: int :: { alloc[x] } x == new || old(alloc)[x] == alloc[x]);



procedure $free(pointer: int);
  modifies alloc;



procedure $alloca(obj_size: int) returns (new: int);
  requires obj_size > 0;
  modifies $CurrAddr, alloc;
  ensures 0 < old($CurrAddr);
  ensures new == old($CurrAddr);
  ensures $CurrAddr > old($CurrAddr) + obj_size;
  ensures $size(new) == obj_size;
  ensures (forall x: int :: new <= x && x < new + obj_size ==> $obj(x) == new);
  ensures alloc[new];
  ensures (forall x: int :: { alloc[x] } x == new || old(alloc)[x] == alloc[x]);



const unique __VERIFIER_assert: int;

const unique main: int;

const unique __VERIFIER_nondet_uint: int;

const unique __VERIFIER_nondet_bool: int;

procedure __VERIFIER_assert(cond: int);
  modifies alloc, $CurrAddr;



implementation __VERIFIER_assert(cond: int)
{
  var $b: bool;

  $bb0:
    assert {:sourcefile "trex03_safe.c"} {:sourceline 1} true;
    assume true;
    assert {:sourcefile "trex03_safe.c"} {:sourceline 2} true;
    $b := cond != 0;
    assert {:sourcefile "trex03_safe.c"} {:sourceline 2} true;
    goto $bb3, $bb4;

  $bb1:
    assert {:sourcefile "trex03_safe.c"} {:sourceline 5} true;
    return;

  $bb2:
    assert {:sourcefile "trex03_safe.c"} {:sourceline 2} true;
    goto $bb5;

  $bb3:
    assert {:sourcefile "trex03_safe.c"} {:sourceline 2} true;
    assume $b;
    goto $bb1;

  $bb4:
    assert {:sourcefile "trex03_safe.c"} {:sourceline 2} true;
    assume !$b;
    goto $bb2;

  $bb5:
    assert {:sourcefile "trex03_safe.c"} {:sourceline 3} true;
    goto $bb5;
}



procedure main() returns ($r: int);
  modifies alloc, $CurrAddr;



implementation main() returns ($r: int)
{
  var $p: int;
  var $p1: int;
  var $p2: int;
  var $b: bool;
  var $p3: int;
  var $b4: bool;
  var $p5: int;
  var $p6: int;
  var $p7: int;
  var $p8: int;
  var $p9: int;
  var $p10: int;
  var $b11: bool;
  var $b12: bool;
  var $b13: bool;
  var $b14: bool;
  var $b15: bool;
  var $b16: bool;
  var $p17: int;
  var $b18: bool;
  var $b19: bool;
  var $p20: int;
  var $p21: int;
  var $p22: int;
  var $p23: int;
  var $p24: int;
  var $p25: int;
  var $b26: bool;
  var $p27: int;
  var $b28: bool;
  var $p29: int;
  var $p30: int;
  var $p31: int;
  var $b32: bool;
  var $b33: bool;
  var v1, v2, v3: int;

  $bb0:
    assert {:sourcefile "trex03_safe.c"} {:sourceline 12} true;
    havoc $p;
    assume $p > 0;
    assert {:sourcefile "trex03_safe.c"} {:sourceline 12} true;
    assume true;
    assert {:sourcefile "trex03_safe.c"} {:sourceline 12} true;
    havoc $p1;
    assume $p1 > 0;
    assert {:sourcefile "trex03_safe.c"} {:sourceline 12} true;
    assume true;
    assert {:sourcefile "trex03_safe.c"} {:sourceline 12} true;
    havoc $p2;
    assume $p2 > 0;
    assert {:sourcefile "trex03_safe.c"} {:sourceline 12} true;
    assume true;
    assert {:sourcefile "trex03_safe.c"} {:sourceline 13} true;
    assume true;
    assert {:sourcefile "trex03_safe.c"} {:sourceline 13} true;
    assume true;
    assert {:sourcefile "trex03_safe.c"} {:sourceline 13} true;
    assume true;
    assert {:sourcefile "trex03_safe.c"} {:sourceline 14} true;
    havoc $b;
    assert {:sourcefile "trex03_safe.c"} {:sourceline 14} true;
    $p3 := $b2p($b);
    assert {:sourcefile "trex03_safe.c"} {:sourceline 14} true;
    assume true;
    assert {:sourcefile "trex03_safe.c"} {:sourceline 14} true;
    havoc $b4;
    assert {:sourcefile "trex03_safe.c"} {:sourceline 14} true;
    $p5 := $b2p($b4);
    assert {:sourcefile "trex03_safe.c"} {:sourceline 14} true;
    assume true;
    assert {:sourcefile "trex03_safe.c"} {:sourceline 16} true;
    $p6 := $p3;
    $p7 := $p2;
    $p8 := $p1;
    $p9 := $p;
    $p10 := $p5;
    goto $bb1;

  $bb1:
    assert b0($p9,$p8,$p7,v1,v2,v3);

    assert {:sourcefile "trex03_safe.c"} {:sourceline 16} true;
    $b11 := $ugt($p9, 0);
    assert {:sourcefile "trex03_safe.c"} {:sourceline 16} true;
    $b12 := false;
    goto $bb4, $bb5;

  $bb2:
    assert {:sourcefile "trex03_safe.c"} {:sourceline 16} true;
    $b32 := $ugt($p8, 0);
    assert {:sourcefile "trex03_safe.c"} {:sourceline 16} true;
    $b12 := false;
    goto $bb28, $bb29;

  $bb3:
    goto $bb8, $bb9;

  $bb4:
    assert {:sourcefile "trex03_safe.c"} {:sourceline 16} true;
    assume $b11;
    goto $bb2;

  $bb5:
    assert {:sourcefile "trex03_safe.c"} {:sourceline 16} true;
    assume !$b11;
    goto $bb3;

  $bb6:
    assert {:sourcefile "trex03_safe.c"} {:sourceline 18} true;
    $b18 := $i2b($p6);
    assert {:sourcefile "trex03_safe.c"} {:sourceline 18} true;
    goto $bb19, $bb20;

  $bb7:
    assert {:sourcefile "trex03_safe.c"} {:sourceline 25} true;
    $b13 := $p9 == 0;
    assert {:sourcefile "trex03_safe.c"} {:sourceline 25} true;
    $b14 := true;
    goto $bb12, $bb13;

  $bb8:
    assume $b12;
    goto $bb6;

  $bb9:
    assume !$b12;
    goto $bb7;

  $bb10:
    assert {:sourcefile "trex03_safe.c"} {:sourceline 25} true;
    $p17 := $b2p($b14);
    assert {:sourcefile "trex03_safe.c"} {:sourceline 25} true;
    assert $p17 == 1;
    assert {:sourcefile "trex03_safe.c"} {:sourceline 26} true;
    $r := 0;
    return;

  $bb11:
    assert {:sourcefile "trex03_safe.c"} {:sourceline 25} true;
    $b15 := $p8 == 0;
    assert {:sourcefile "trex03_safe.c"} {:sourceline 25} true;
    $b14 := true;
    goto $bb15, $bb16;

  $bb12:
    assert {:sourcefile "trex03_safe.c"} {:sourceline 25} true;
    assume $b13;
    goto $bb10;

  $bb13:
    assert {:sourcefile "trex03_safe.c"} {:sourceline 25} true;
    assume !$b13;
    goto $bb11;

  $bb14:
    assert {:sourcefile "trex03_safe.c"} {:sourceline 25} true;
    $b16 := $p7 == 0;
    assert {:sourcefile "trex03_safe.c"} {:sourceline 25} true;
    $b14 := $b16;
    goto $bb10;

  $bb15:
    assert {:sourcefile "trex03_safe.c"} {:sourceline 25} true;
    assume $b15;
    goto $bb10;

  $bb16:
    assert {:sourcefile "trex03_safe.c"} {:sourceline 25} true;
    assume !$b15;
    goto $bb14;

  $bb17:
    assert {:sourcefile "trex03_safe.c"} {:sourceline 18} true;
    $p31 := $sub($p9, 1);
    assert {:sourcefile "trex03_safe.c"} {:sourceline 18} true;
    assume true;
    assert {:sourcefile "trex03_safe.c"} {:sourceline 18} true;
    $p23 := $p7;
    $p24 := $p8;
    $p25 := $p31;
    goto $bb26;

  $bb18:
    assert {:sourcefile "trex03_safe.c"} {:sourceline 19} true;
    $b19 := $i2b($p10);
    assert {:sourcefile "trex03_safe.c"} {:sourceline 19} true;
    goto $bb23, $bb24;

  $bb19:
    assert {:sourcefile "trex03_safe.c"} {:sourceline 18} true;
    assume $b18;
    goto $bb17;

  $bb20:
    assert {:sourcefile "trex03_safe.c"} {:sourceline 18} true;
    assume !$b18;
    goto $bb18;

  $bb21:
    assert {:sourcefile "trex03_safe.c"} {:sourceline 19} true;
    $p30 := $sub($p8, 1);
    assert {:sourcefile "trex03_safe.c"} {:sourceline 19} true;
    assume true;
    assert {:sourcefile "trex03_safe.c"} {:sourceline 19} true;
    $p21 := $p7;
    $p22 := $p30;
    goto $bb25;

  $bb22:
    assert {:sourcefile "trex03_safe.c"} {:sourceline 20} true;
    $p20 := $sub($p7, 1);
    assert {:sourcefile "trex03_safe.c"} {:sourceline 20} true;
    assume true;
    $p21 := $p20;
    $p22 := $p8;
    goto $bb25;

  $bb23:
    assert {:sourcefile "trex03_safe.c"} {:sourceline 19} true;
    assume $b19;
    goto $bb21;

  $bb24:
    assert {:sourcefile "trex03_safe.c"} {:sourceline 19} true;
    assume !$b19;
    goto $bb22;

  $bb25:
    $p23 := $p21;
    $p24 := $p22;
    $p25 := $p9;
    goto $bb26;

  $bb26:
    assert {:sourcefile "trex03_safe.c"} {:sourceline 21} true;
    havoc $b26;
    assert {:sourcefile "trex03_safe.c"} {:sourceline 21} true;
    $p27 := $b2p($b26);
    assert {:sourcefile "trex03_safe.c"} {:sourceline 21} true;
    assume true;
    assert {:sourcefile "trex03_safe.c"} {:sourceline 22} true;
    havoc $b28;
    assert {:sourcefile "trex03_safe.c"} {:sourceline 22} true;
    $p29 := $b2p($b28);
    havoc v1;
    havoc v2;
    havoc v3;

    assert {:sourcefile "trex03_safe.c"} {:sourceline 22} true;
    assume true;
    assert {:sourcefile "trex03_safe.c"} {:sourceline 23} true;
    $p6 := $p27;
    $p7 := $p23;
    $p8 := $p24;
    $p9 := $p25;
    $p10 := $p29;
    goto $bb1;

  $bb27:
    assert {:sourcefile "trex03_safe.c"} {:sourceline 16} true;
    $b33 := $ugt($p7, 0);
    $b12 := $b33;
    goto $bb3;

  $bb28:
    assert {:sourcefile "trex03_safe.c"} {:sourceline 16} true;
    assume $b32;
    goto $bb27;

  $bb29:
    assert {:sourcefile "trex03_safe.c"} {:sourceline 16} true;
    assume !$b32;
    goto $bb3;
}



procedure __VERIFIER_nondet_uint() returns ($r: int);
  modifies alloc, $CurrAddr;



procedure __VERIFIER_nondet_bool() returns ($r: bool);
  modifies alloc, $CurrAddr;


