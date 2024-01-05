/*
 * Program used in the experimental evaluation of the following paper:
 * De Nicola, Di Stefano, Inverso. Multi-Agent Systems With Virtual Stigmergies. Sci.Comp. Progr. 187, 2020
 *
 * Date: 2020
 * Authors: Luca Di Stefano, Omar Inverso
 * Contact: luca <dot> distefano <at> gssi <dot> it
 */
extern int __VERIFIER_nondet_int(void);
typedef char TYPEOFVALUES;
typedef unsigned char TYPEOFPC;
typedef unsigned char TYPEOFAGENTID;
typedef unsigned char TYPEOFKEYIID;
typedef unsigned char TYPEOFKEYEID;
TYPEOFVALUES I_0;
TYPEOFVALUES I_1;
TYPEOFVALUES I_2;
TYPEOFVALUES E_0;
TYPEOFVALUES E_1;
TYPEOFVALUES E_2;
TYPEOFVALUES E_3;
unsigned char pc_0;
unsigned char pc_1;
unsigned char pc_2;
TYPEOFVALUES _I_21_1_0;
TYPEOFVALUES _I_21_1_1;
TYPEOFVALUES _I_21_1_2;
TYPEOFVALUES _E_21_1_0;
TYPEOFVALUES _E_21_1_1;
TYPEOFVALUES _E_21_1_2;
TYPEOFVALUES _E_21_1_3;
TYPEOFPC _pc_21_1_0;
TYPEOFPC _pc_21_1_1;
TYPEOFPC _pc_21_1_2;
void setpc(int x0, int x1, unsigned value)
{
  switch ((3 * x0) + x1)
  {
    case 0:
      pc_0 = value;
      break;

    case 1:
      pc_1 = value;
      break;

    case 2:
      pc_2 = value;
      break;

  }

}

TYPEOFVALUES getE(int x0)
{
  switch (x0)
  {
    case 0:
      return E_0;

    case 1:
      return E_1;

    case 2:
      return E_2;

    case 3:
      return E_3;

  }

}

TYPEOFVALUES get_I_21_1(int x0, int x1)
{
  switch ((3 * x0) + x1)
  {
    case 0:
      return _I_21_1_0;

    case 1:
      return _I_21_1_1;

    case 2:
      return _I_21_1_2;

  }

}

TYPEOFPC get_pc_21_1(int x0, int x1)
{
  switch ((3 * x0) + x1)
  {
    case 0:
      return _pc_21_1_0;

    case 1:
      return _pc_21_1_1;

    case 2:
      return _pc_21_1_2;

  }

}

unsigned char getpc(int x0, int x1)
{
  switch ((3 * x0) + x1)
  {
    case 0:
      return pc_0;

    case 1:
      return pc_1;

    case 2:
      return pc_2;

  }

}

TYPEOFVALUES get_E_21_1(int x0)
{
  switch (x0)
  {
    case 0:
      return _E_21_1_0;

    case 1:
      return _E_21_1_1;

    case 2:
      return _E_21_1_2;

    case 3:
      return _E_21_1_3;

  }

}

TYPEOFVALUES getI(int x0, int x1)
{
  switch ((3 * x0) + x1)
  {
    case 0:
      return I_0;

    case 1:
      return I_1;

    case 2:
      return I_2;

  }

}

void setI(int x0, int x1, TYPEOFVALUES value)
{
  switch ((3 * x0) + x1)
  {
    case 0:
      I_0 = value;
      break;

    case 1:
      I_1 = value;
      break;

    case 2:
      I_2 = value;
      break;

  }

}

void attr(TYPEOFAGENTID id, TYPEOFKEYIID key, TYPEOFVALUES value, _Bool check)
{
  setI(id, key, value);
}

void _0_13(int tid)
{
  __VERIFIER_assume(getE(0) != tid);
  __VERIFIER_assume(getE(1) == 1);
  __VERIFIER_assume((getE(2) == 3) && (getI(tid, 0) == 2));
  TYPEOFVALUES val0 = 3;
  attr(tid, 0, val0, 1);
  setpc(tid, 0, 12);
}

void _0_6(int tid)
{
  TYPEOFVALUES val0 = 2;
  attr(tid, 0, val0, 1);
  setpc(tid, 0, 5);
}

void _0_3(int tid)
{
  __VERIFIER_assume((getE(1) == 2) && (getE(0) == tid));
  __VERIFIER_assume((getI(tid, 0) == 1) && (getE(3) == 0));
  TYPEOFVALUES val0 = 3;
  attr(tid, 0, val0, 1);
  setpc(tid, 0, 2);
}

void _0_11(int tid)
{
  __VERIFIER_assume(getE(0) != tid);
  __VERIFIER_assume(getE(1) == 1);
  __VERIFIER_assume((getE(2) == 0) && (getI(tid, 0) == 3));
  TYPEOFVALUES val0 = 2;
  attr(tid, 0, val0, 1);
  setpc(tid, 0, 10);
}

void _0_9(int tid)
{
  __VERIFIER_assume(getE(0) != tid);
  __VERIFIER_assume(getE(1) == 1);
  __VERIFIER_assume((getE(2) == 1) && (getI(tid, 0) == 2));
  TYPEOFVALUES val0 = 3;
  attr(tid, 0, val0, 1);
  setpc(tid, 0, 8);
}

void setE(int x0, TYPEOFVALUES value)
{
  switch (x0)
  {
    case 0:
      E_0 = value;
      break;

    case 1:
      E_1 = value;
      break;

    case 2:
      E_2 = value;
      break;

    case 3:
      E_3 = value;
      break;

  }

}

void init()
{
  ;
  ;
  ;
  unsigned char i = __VERIFIER_nondet_int();
  unsigned char j = __VERIFIER_nondet_int();
  __VERIFIER_assume((((((get_pc_21_1(0, 0) == 3) || (get_pc_21_1(0, 0) == 4)) || (get_pc_21_1(0, 0) == 7)) || (get_pc_21_1(0, 0) == 9)) || (get_pc_21_1(0, 0) == 11)) || (get_pc_21_1(0, 0) == 13));
  __VERIFIER_assume((((((get_pc_21_1(1, 0) == 3) || (get_pc_21_1(1, 0) == 4)) || (get_pc_21_1(1, 0) == 7)) || (get_pc_21_1(1, 0) == 9)) || (get_pc_21_1(1, 0) == 11)) || (get_pc_21_1(1, 0) == 13));
  __VERIFIER_assume((((((get_pc_21_1(2, 0) == 3) || (get_pc_21_1(2, 0) == 4)) || (get_pc_21_1(2, 0) == 7)) || (get_pc_21_1(2, 0) == 9)) || (get_pc_21_1(2, 0) == 11)) || (get_pc_21_1(2, 0) == 13));
  __VERIFIER_assume(get_E_21_1(0) == (-1));
  __VERIFIER_assume(get_E_21_1(1) == 0);
  __VERIFIER_assume(get_E_21_1(2) == (-1));
  __VERIFIER_assume(get_E_21_1(3) == (-1));
  __VERIFIER_assume(get_I_21_1(0, 0) == 0);
  __VERIFIER_assume(get_I_21_1(1, 0) == 0);
  __VERIFIER_assume(get_I_21_1(2, 0) == 1);
  for (i = 0; i < 4; i++)
  {
    setE(i, get_E_21_1(i));
  }

  for (i = 0; i < 3; i++)
  {
    for (j = 0; j < 1; j++)
    {
      setpc(i, j, get_pc_21_1(i, j));
    }

    for (j = 0; j < 1; j++)
    {
      setI(i, j, get_I_21_1(i, j));
    }

  }

}

void env(TYPEOFAGENTID id, TYPEOFKEYEID key, TYPEOFVALUES value, _Bool check)
{
  setE(key, value);
}

void _0_7(int tid)
{
  __VERIFIER_assume(getE(0) != tid);
  __VERIFIER_assume(getE(1) == 1);
  __VERIFIER_assume((getE(2) == 1) && (getI(tid, 0) == 0));
  TYPEOFVALUES val0 = 2;
  TYPEOFVALUES val1 = getI(tid, 0);
  env(tid, 1, val0, 1);
  env(tid, 3, val1, 0);
  setpc(tid, 0, 6);
}

void _0_8(int tid)
{
  TYPEOFVALUES val0 = -1;
  TYPEOFVALUES val1 = 0;
  env(tid, 0, val0, 1);
  env(tid, 1, val1, 0);
  TYPEOFPC pc0 = __VERIFIER_nondet_int();
  __VERIFIER_assume((((((pc0 == 3) || (pc0 == 4)) || (pc0 == 7)) || (pc0 == 9)) || (pc0 == 11)) || (pc0 == 13));
  setpc(tid, 0, pc0);
}

void _0_2(int tid)
{
  TYPEOFVALUES val0 = 3;
  env(tid, 1, val0, 1);
  TYPEOFPC pc0 = __VERIFIER_nondet_int();
  __VERIFIER_assume((((((pc0 == 3) || (pc0 == 4)) || (pc0 == 7)) || (pc0 == 9)) || (pc0 == 11)) || (pc0 == 13));
  setpc(tid, 0, pc0);
}

void _0_12(int tid)
{
  TYPEOFVALUES val0 = -1;
  TYPEOFVALUES val1 = 0;
  env(tid, 0, val0, 1);
  env(tid, 1, val1, 0);
  TYPEOFPC pc0 = __VERIFIER_nondet_int();
  __VERIFIER_assume((((((pc0 == 3) || (pc0 == 4)) || (pc0 == 7)) || (pc0 == 9)) || (pc0 == 11)) || (pc0 == 13));
  setpc(tid, 0, pc0);
}

void _0_5(int tid)
{
  __VERIFIER_assume(getE(1) == 3);
  TYPEOFVALUES val0 = -1;
  TYPEOFVALUES val1 = -1;
  TYPEOFVALUES val2 = 0;
  env(tid, 0, val0, 1);
  env(tid, 3, val1, 0);
  env(tid, 1, val2, 0);
  TYPEOFPC pc0 = __VERIFIER_nondet_int();
  __VERIFIER_assume((((((pc0 == 3) || (pc0 == 4)) || (pc0 == 7)) || (pc0 == 9)) || (pc0 == 11)) || (pc0 == 13));
  setpc(tid, 0, pc0);
}

void _0_4(int tid)
{
  __VERIFIER_assume(getE(0) != tid);
  __VERIFIER_assume(getE(1) == 0);
  __VERIFIER_assume(getI(tid, 0) != 2);
  TYPEOFVALUES val0 = tid;
  TYPEOFVALUES val1 = getI(tid, 0);
  TYPEOFVALUES val2 = 1;
  env(tid, 0, val0, 1);
  env(tid, 2, val1, 0);
  env(tid, 1, val2, 0);
  TYPEOFPC pc0 = __VERIFIER_nondet_int();
  __VERIFIER_assume((((((pc0 == 3) || (pc0 == 4)) || (pc0 == 7)) || (pc0 == 9)) || (pc0 == 11)) || (pc0 == 13));
  setpc(tid, 0, pc0);
}

void _0_10(int tid)
{
  TYPEOFVALUES val0 = -1;
  TYPEOFVALUES val1 = 0;
  env(tid, 0, val0, 1);
  env(tid, 1, val1, 0);
  TYPEOFPC pc0 = __VERIFIER_nondet_int();
  __VERIFIER_assume((((((pc0 == 3) || (pc0 == 4)) || (pc0 == 7)) || (pc0 == 9)) || (pc0 == 11)) || (pc0 == 13));
  setpc(tid, 0, pc0);
}

int main(void)
{
  init();
  TYPEOFAGENTID firstAgent = __VERIFIER_nondet_int();
  while (1)
  {
    TYPEOFAGENTID newagent = __VERIFIER_nondet_int();
    __VERIFIER_assume(newagent < 3);
    firstAgent = newagent;
    __VERIFIER_assume(firstAgent < 3);
    switch (getpc(firstAgent, 0))
    {
      case 2:
        _0_2(firstAgent);
        break;

      case 3:
        _0_3(firstAgent);
        break;

      case 4:
        _0_4(firstAgent);
        break;

      case 5:
        _0_5(firstAgent);
        break;

      case 6:
        _0_6(firstAgent);
        break;

      case 7:
        _0_7(firstAgent);
        break;

      case 8:
        _0_8(firstAgent);
        break;

      case 9:
        _0_9(firstAgent);
        break;

      case 10:
        _0_10(firstAgent);
        break;

      case 11:
        _0_11(firstAgent);
        break;

      case 12:
        _0_12(firstAgent);
        break;

      case 13:
        _0_13(firstAgent);
        break;

      default:
      {
      }

    }

    if ((((getI(2, 0) == 0) || (getI(2, 0) == 2)) && ((getI(0, 0) == 0) || (getI(0, 0) == 2))) && ((getI(1, 0) == 0) || (getI(1, 0) == 2)))
    {
      return 0;
    }

  }

}


