procedure boogie_si_record_int(i: int);

function {:existential true} b0(i:int, sn:int): bool;


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

procedure __VERIFIER_assert(cond: int);
  modifies alloc, $CurrAddr;



implementation __VERIFIER_assert(cond: int)
{
  var $b: bool;

  $bb0:
    assert {:sourcefile "sum04_safe.c"} {:sourceline 1} true;
    assume true;
    assert {:sourcefile "sum04_safe.c"} {:sourceline 2} true;
    $b := cond != 0;
    assert {:sourcefile "sum04_safe.c"} {:sourceline 2} true;
    goto $bb3, $bb4;

  $bb1:
    assert {:sourcefile "sum04_safe.c"} {:sourceline 5} true;
    return;

  $bb2:
    assert {:sourcefile "sum04_safe.c"} {:sourceline 2} true;
    goto $bb5;

  $bb3:
    assert {:sourcefile "sum04_safe.c"} {:sourceline 2} true;
    assume $b;
    goto $bb1;

  $bb4:
    assert {:sourcefile "sum04_safe.c"} {:sourceline 2} true;
    assume !$b;
    goto $bb2;

  $bb5:
    assert {:sourcefile "sum04_safe.c"} {:sourceline 3} true;
    goto $bb5;
}



procedure main() returns ($r: int);
  modifies alloc, $CurrAddr;



implementation main() returns ($r: int)
{
  var $p: int;
  var $p1: int;
  var $b: bool;
  var $b2: bool;
  var $b3: bool;
  var $b4: bool;
  var $p5: int;
  var $p6: int;
  var $p7: int;

  $bb0:
    assert {:sourcefile "sum04_safe.c"} {:sourceline 10} true;
    assume true;
    assert {:sourcefile "sum04_safe.c"} {:sourceline 11} true;
    assume true;
    assert {:sourcefile "sum04_safe.c"} {:sourceline 11} true;
    $p := 1;
    $p1 := 0;
    goto $bb1;

  $bb1:
    //assert $p1 == 2*$p - 2;
    //assert 0 <= $p && $p <= 9;
    assert b0($p,$p1);
    //assert $p1 == $p - 1 && $p1 <= 8;

    assert {:sourcefile "sum04_safe.c"} {:sourceline 11} true;
    $b := $sle($p, 8);
    assert {:sourcefile "sum04_safe.c"} {:sourceline 11} true;
    goto $bb4, $bb5;

  $bb2:
    assert {:sourcefile "sum04_safe.c"} {:sourceline 12} true;
    $p6 := $add($p1, 1);
    assert {:sourcefile "sum04_safe.c"} {:sourceline 12} true;
    assume true;
    assert {:sourcefile "sum04_safe.c"} {:sourceline 13} true;
    goto $bb10;

  $bb3:
    assert {:sourcefile "sum04_safe.c"} {:sourceline 14} true;
    $b2 := $p1 == 8;
    assert {:sourcefile "sum04_safe.c"} {:sourceline 14} true;
    $b3 := true;
    goto $bb8, $bb9;

  $bb4:
    assert {:sourcefile "sum04_safe.c"} {:sourceline 11} true;
    assume $b;
    goto $bb2;

  $bb5:
    assert {:sourcefile "sum04_safe.c"} {:sourceline 11} true;
    assume !$b;
    goto $bb3;

  $bb6:
    assert {:sourcefile "sum04_safe.c"} {:sourceline 14} true;
    $p5 := $b2p($b3);
    assert {:sourcefile "sum04_safe.c"} {:sourceline 14} true;
    assert $p5 == 1;
    assert {:sourcefile "sum04_safe.c"} {:sourceline 15} true;
    $r := 0;
    return;

  $bb7:
    assert {:sourcefile "sum04_safe.c"} {:sourceline 14} true;
    $b4 := $p1 == 0;
    assert {:sourcefile "sum04_safe.c"} {:sourceline 14} true;
    $b3 := $b4;
    goto $bb6;

  $bb8:
    assert {:sourcefile "sum04_safe.c"} {:sourceline 14} true;
    assume $b2;
    goto $bb6;

  $bb9:
    assert {:sourcefile "sum04_safe.c"} {:sourceline 14} true;
    assume !$b2;
    goto $bb7;

  $bb10:
    assert {:sourcefile "sum04_safe.c"} {:sourceline 11} true;
    $p7 := $add($p, 1);
    assert {:sourcefile "sum04_safe.c"} {:sourceline 11} true;
    assume true;
    assert {:sourcefile "sum04_safe.c"} {:sourceline 11} true;
    $p := $p7;
    $p1 := $p6;
    goto $bb1;
}


