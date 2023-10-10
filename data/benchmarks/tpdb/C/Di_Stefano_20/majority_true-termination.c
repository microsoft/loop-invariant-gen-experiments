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

TYPEOFVALUES I[3][1];
TYPEOFVALUES E[4];
unsigned char pc[3][1];
void attr(TYPEOFAGENTID id, TYPEOFKEYIID key, TYPEOFVALUES value, _Bool check)
{
  I[id][key] = value;
}

void env(TYPEOFAGENTID id, TYPEOFKEYEID key, TYPEOFVALUES value, _Bool check)
{
  E[key] = value;
}

void init()
{
  TYPEOFVALUES _I[3][1];
  TYPEOFVALUES _E[4];
  TYPEOFPC _pc[3][1];
  unsigned char i = __VERIFIER_nondet_int();
  unsigned char j = __VERIFIER_nondet_int();

  __VERIFIER_assume((((((_pc[0][0] == 3) || (_pc[0][0] == 4)) || (_pc[0][0] == 7)) || (_pc[0][0] == 9)) || (_pc[0][0] == 11)) || (_pc[0][0] == 13));
  __VERIFIER_assume((((((_pc[1][0] == 3) || (_pc[1][0] == 4)) || (_pc[1][0] == 7)) || (_pc[1][0] == 9)) || (_pc[1][0] == 11)) || (_pc[1][0] == 13));
  __VERIFIER_assume((((((_pc[2][0] == 3) || (_pc[2][0] == 4)) || (_pc[2][0] == 7)) || (_pc[2][0] == 9)) || (_pc[2][0] == 11)) || (_pc[2][0] == 13));
  __VERIFIER_assume(_E[0] == (-1));
  __VERIFIER_assume(_E[1] == 0);
  __VERIFIER_assume(_E[2] == (-1));
  __VERIFIER_assume(_E[3] == (-1));
  __VERIFIER_assume(_I[0][0] == 0);
  __VERIFIER_assume(_I[1][0] == 0);
  __VERIFIER_assume(_I[2][0] == 1);
  for (i = 0; i < 4; i++)
  {
    E[i] = _E[i];
  }

  for (i = 0; i < 3; i++)
  {
    for (j = 0; j < 1; j++)
    {
      pc[i][j] = _pc[i][j];
    }

    for (j = 0; j < 1; j++)
    {
      I[i][j] = _I[i][j];
    }

  }

}

void _0_2(int tid)
{
  TYPEOFVALUES val0 = 3;
  env(tid, 1, val0, 1);
  TYPEOFPC pc0 = __VERIFIER_nondet_int();
  __VERIFIER_assume((((((pc0 == 3) || (pc0 == 4)) || (pc0 == 7)) || (pc0 == 9)) || (pc0 == 11)) || (pc0 == 13));
  pc[tid][0] = pc0;
}

void _0_3(int tid)
{
  __VERIFIER_assume((E[1] == 2) && (E[0] == tid));
  __VERIFIER_assume((I[tid][0] == 1) && (E[3] == 0));
  TYPEOFVALUES val0 = 3;
  attr(tid, 0, val0, 1);
  pc[tid][0] = 2;
}

void _0_4(int tid)
{
  __VERIFIER_assume(E[0] != tid);
  __VERIFIER_assume(E[1] == 0);
  __VERIFIER_assume(I[tid][0] != 2);
  TYPEOFVALUES val0 = tid;
  TYPEOFVALUES val1 = I[tid][0];
  TYPEOFVALUES val2 = 1;
  env(tid, 0, val0, 1);
  env(tid, 2, val1, 0);
  env(tid, 1, val2, 0);
  TYPEOFPC pc0 = __VERIFIER_nondet_int();
  __VERIFIER_assume((((((pc0 == 3) || (pc0 == 4)) || (pc0 == 7)) || (pc0 == 9)) || (pc0 == 11)) || (pc0 == 13));
  pc[tid][0] = pc0;
}

void _0_5(int tid)
{
  __VERIFIER_assume(E[1] == 3);
  TYPEOFVALUES val0 = -1;
  TYPEOFVALUES val1 = -1;
  TYPEOFVALUES val2 = 0;
  env(tid, 0, val0, 1);
  env(tid, 3, val1, 0);
  env(tid, 1, val2, 0);
  TYPEOFPC pc0 = __VERIFIER_nondet_int();
  __VERIFIER_assume((((((pc0 == 3) || (pc0 == 4)) || (pc0 == 7)) || (pc0 == 9)) || (pc0 == 11)) || (pc0 == 13));
  pc[tid][0] = pc0;
}

void _0_6(int tid)
{
  TYPEOFVALUES val0 = 2;
  attr(tid, 0, val0, 1);
  pc[tid][0] = 5;
}

void _0_7(int tid)
{
  __VERIFIER_assume(E[0] != tid);
  __VERIFIER_assume(E[1] == 1);
  __VERIFIER_assume((E[2] == 1) && (I[tid][0] == 0));
  TYPEOFVALUES val0 = 2;
  TYPEOFVALUES val1 = I[tid][0];
  env(tid, 1, val0, 1);
  env(tid, 3, val1, 0);
  pc[tid][0] = 6;
}

void _0_8(int tid)
{
  TYPEOFVALUES val0 = -1;
  TYPEOFVALUES val1 = 0;
  env(tid, 0, val0, 1);
  env(tid, 1, val1, 0);
  TYPEOFPC pc0 = __VERIFIER_nondet_int();
  __VERIFIER_assume((((((pc0 == 3) || (pc0 == 4)) || (pc0 == 7)) || (pc0 == 9)) || (pc0 == 11)) || (pc0 == 13));
  pc[tid][0] = pc0;
}

void _0_9(int tid)
{
  __VERIFIER_assume(E[0] != tid);
  __VERIFIER_assume(E[1] == 1);
  __VERIFIER_assume((E[2] == 1) && (I[tid][0] == 2));
  TYPEOFVALUES val0 = 3;
  attr(tid, 0, val0, 1);
  pc[tid][0] = 8;
}

void _0_10(int tid)
{
  TYPEOFVALUES val0 = -1;
  TYPEOFVALUES val1 = 0;
  env(tid, 0, val0, 1);
  env(tid, 1, val1, 0);
  TYPEOFPC pc0 = __VERIFIER_nondet_int();
  __VERIFIER_assume((((((pc0 == 3) || (pc0 == 4)) || (pc0 == 7)) || (pc0 == 9)) || (pc0 == 11)) || (pc0 == 13));
  pc[tid][0] = pc0;
}

void _0_11(int tid)
{
  __VERIFIER_assume(E[0] != tid);
  __VERIFIER_assume(E[1] == 1);
  __VERIFIER_assume((E[2] == 0) && (I[tid][0] == 3));
  TYPEOFVALUES val0 = 2;
  attr(tid, 0, val0, 1);
  pc[tid][0] = 10;
}

void _0_12(int tid)
{
  TYPEOFVALUES val0 = -1;
  TYPEOFVALUES val1 = 0;
  env(tid, 0, val0, 1);
  env(tid, 1, val1, 0);
  TYPEOFPC pc0 = __VERIFIER_nondet_int();
  __VERIFIER_assume((((((pc0 == 3) || (pc0 == 4)) || (pc0 == 7)) || (pc0 == 9)) || (pc0 == 11)) || (pc0 == 13));
  pc[tid][0] = pc0;
}

void _0_13(int tid)
{
  __VERIFIER_assume(E[0] != tid);
  __VERIFIER_assume(E[1] == 1);
  __VERIFIER_assume((E[2] == 3) && (I[tid][0] == 2));
  TYPEOFVALUES val0 = 3;
  attr(tid, 0, val0, 1);
  pc[tid][0] = 12;
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
    switch (pc[firstAgent][0])
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

    if ((((I[2][0] == 0) || (I[2][0] == 2)) && ((I[0][0] == 0) || (I[0][0] == 2))) && ((I[1][0] == 0) || (I[1][0] == 2)))
    {
      return 0;
    }

  }
}


