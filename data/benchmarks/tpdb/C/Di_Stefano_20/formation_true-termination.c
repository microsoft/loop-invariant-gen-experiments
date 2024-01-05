/*
 * Date: 2020
 * Authors: Luca Di Stefano, Omar Inverso
 * Contact: luca <dot> distefano <at> gssi <dot> it
 */
extern int __VERIFIER_nondet_int(void);
typedef char TYPEOFVALUES;
typedef unsigned char TYPEOFPC;
typedef unsigned char TYPEOFTIME;
typedef unsigned char TYPEOFAGENTID;
typedef unsigned char TYPEOFKEYIID;
typedef unsigned char TYPEOFKEYLID;
TYPEOFVALUES __abs(TYPEOFVALUES x)
{
  return (x > 0) ? (x) : (-x);
}

TYPEOFVALUES I[3][1];
TYPEOFPC pc[3][1];
TYPEOFTIME __LABS_time;
_Bool Hin[3][2];
_Bool Hout[3][2];
unsigned char HinCnt[3];
unsigned char HoutCnt[3];
TYPEOFTIME now(void)
{
  return ++__LABS_time;
}

TYPEOFVALUES Lvalue[3][2];
TYPEOFTIME Ltstamp[3][2];
const TYPEOFKEYLID tupleStart[2] = {0, 1};
const TYPEOFKEYLID tupleEnd[2] = {0, 1};
_Bool link(TYPEOFAGENTID __LABS_link1, TYPEOFAGENTID __LABS_link2, TYPEOFKEYLID key)
{
  _Bool __LABS_link = 0;
  if ((key >= 0) && (key <= 0))
  {
    __LABS_link = ((I[__LABS_link1][0] - I[__LABS_link2][0]) >= 0) && ((I[__LABS_link1][0] - I[__LABS_link2][0]) <= 2);
  }
  else
    if ((key >= 1) && (key <= 1))
  {
    __LABS_link = ((I[__LABS_link2][0] - I[__LABS_link1][0]) > 0) && ((I[__LABS_link2][0] - I[__LABS_link1][0]) <= 2);
  }


  return __LABS_link;
}

TYPEOFTIME timeof(TYPEOFAGENTID id, TYPEOFKEYLID key)
{
  return Ltstamp[id][tupleStart[key]];
}

void setHin(TYPEOFAGENTID id, TYPEOFKEYLID key)
{
  HinCnt[id] = HinCnt[id] + (!Hin[id][tupleStart[key]]);
  Hin[id][tupleStart[key]] = 1;
}

void clearHin(TYPEOFAGENTID id, TYPEOFKEYLID key)
{
  HinCnt[id] = HinCnt[id] - Hin[id][tupleStart[key]];
  Hin[id][tupleStart[key]] = 0;
}

void setHout(TYPEOFAGENTID id, TYPEOFKEYLID key)
{
  HoutCnt[id] = HoutCnt[id] + (!Hout[id][tupleStart[key]]);
  Hout[id][tupleStart[key]] = 1;
}

void clearHout(TYPEOFAGENTID id, TYPEOFKEYLID key)
{
  HoutCnt[id] = HoutCnt[id] - Hout[id][tupleStart[key]];
  Hout[id][tupleStart[key]] = 0;
}

void attr(TYPEOFAGENTID id, TYPEOFKEYIID key, TYPEOFVALUES value, _Bool check)
{
  __VERIFIER_assume((!check) || (HoutCnt[id] == 0));
  __VERIFIER_assume((!check) || (HinCnt[id] == 0));
  I[id][key] = value;
  now();
}

void lstig(TYPEOFAGENTID id, TYPEOFKEYLID key, TYPEOFVALUES value, _Bool check)
{
  __VERIFIER_assume((!check) || (HoutCnt[id] == 0));
  __VERIFIER_assume((!check) || (HinCnt[id] == 0));
  Lvalue[id][key] = value;
  Ltstamp[id][tupleStart[key]] = now();
  setHout(id, key);
}

void confirm(void)
{
  TYPEOFAGENTID guessedcomp = __VERIFIER_nondet_int();
  __VERIFIER_assume(guessedcomp < 3);
  __VERIFIER_assume(HinCnt[guessedcomp] > 0);
  TYPEOFKEYLID guessedkey = __VERIFIER_nondet_int();
  __VERIFIER_assume(guessedkey < 2);
  __VERIFIER_assume(Hin[guessedcomp][guessedkey] == 1);
  TYPEOFAGENTID i = __VERIFIER_nondet_int();
  TYPEOFTIME t = timeof(guessedcomp, guessedkey);
  for (i = 0; i < 3; i++)
  {
    if (((guessedcomp != i) && (timeof(i, guessedkey) != t)) && link(guessedcomp, i, guessedkey))
    {
      setHout(i, guessedkey);
      if (timeof(i, guessedkey) < t)
      {
        TYPEOFKEYLID k = __VERIFIER_nondet_int();
        TYPEOFKEYLID next = __VERIFIER_nondet_int();
        clearHin(i, guessedkey);
        for (k = 0; k < 1; k++)
        {
          next = guessedkey + k;
          if (next <= tupleEnd[guessedkey])
            Lvalue[i][next] = Lvalue[guessedcomp][next];

        }

        Ltstamp[i][guessedkey] = t;
      }

    }

  }

  clearHin(guessedcomp, guessedkey);
}

void propagate(void)
{
  TYPEOFAGENTID guessedcomp = __VERIFIER_nondet_int();
  __VERIFIER_assume(guessedcomp < 3);
  __VERIFIER_assume(HoutCnt[guessedcomp] > 0);
  TYPEOFKEYLID guessedkey = __VERIFIER_nondet_int();
  __VERIFIER_assume(guessedkey < 2);
  __VERIFIER_assume(Hout[guessedcomp][guessedkey] == 1);
  TYPEOFAGENTID i = __VERIFIER_nondet_int();
  TYPEOFTIME t = timeof(guessedcomp, guessedkey);
  for (i = 0; i < 3; i++)
  {
    if (((guessedcomp != i) && (timeof(i, guessedkey) < t)) && link(guessedcomp, i, guessedkey))
    {
      setHout(i, guessedkey);
      clearHin(i, guessedkey);
      TYPEOFKEYLID k = __VERIFIER_nondet_int();
      TYPEOFKEYLID next = __VERIFIER_nondet_int();
      for (k = 0; k < 1; k++)
      {
        next = guessedkey + k;
        if (next <= tupleEnd[guessedkey])
          Lvalue[i][next] = Lvalue[guessedcomp][next];

      }

      Ltstamp[i][guessedkey] = t;
    }

  }

  clearHout(guessedcomp, guessedkey);
}

void init()
{
  TYPEOFVALUES _I[3][1];
  TYPEOFPC _pc[3][1];
  TYPEOFVALUES _Lvalue[3][2];
  unsigned char i = __VERIFIER_nondet_int();
  unsigned char j = __VERIFIER_nondet_int();
  for (i = 0; i < 3; i++)
  {
    for (j = 0; j < 2; j++)
    {
      Ltstamp[i][j] = 0;
      Hin[i][j] = 0;
      Hout[i][j] = 0;
    }

    HinCnt[i] = 0;
    HoutCnt[i] = 0;
  }

  _pc[0][0] = 6;
  _pc[1][0] = 6;
  _pc[2][0] = 6;
  __VERIFIER_assume(_Lvalue[0][0] == (-128));
  __VERIFIER_assume(_Lvalue[1][0] == (-128));
  __VERIFIER_assume(_Lvalue[2][0] == (-128));
  __VERIFIER_assume(_Lvalue[0][1] == (-128));
  __VERIFIER_assume(_Lvalue[1][1] == (-128));
  __VERIFIER_assume(_Lvalue[2][1] == (-128));
  __VERIFIER_assume((_I[0][0] >= 1) && (_I[0][0] < 10));
  __VERIFIER_assume((_I[1][0] >= 1) && (_I[1][0] < 10));
  __VERIFIER_assume((_I[2][0] >= 1) && (_I[2][0] < 10));
  Ltstamp[0][tupleStart[0]] = now();
  Ltstamp[1][tupleStart[0]] = now();
  Ltstamp[2][tupleStart[0]] = now();
  Ltstamp[0][tupleStart[1]] = now();
  Ltstamp[1][tupleStart[1]] = now();
  Ltstamp[2][tupleStart[1]] = now();
  now();

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

    for (j = 0; j < 2; j++)
    {
      Lvalue[i][j] = _Lvalue[i][j];
    }

  }

}

void _0_2(int tid)
{
  __VERIFIER_assume((Lvalue[tid][0] != tid) && (Lvalue[tid][0] != (-128)));
  __VERIFIER_assume(I[tid][0] > 0);
  TYPEOFVALUES val0 = I[tid][0] - 1;
  attr(tid, 0, val0, 1);
  setHin(tid, 0);
  pc[tid][0] = 6;
}

void _0_3(int tid)
{
  __VERIFIER_assume((Lvalue[tid][0] != tid) && (Lvalue[tid][0] != (-128)));
  __VERIFIER_assume(I[tid][0] == 0);
  TYPEOFVALUES val0 = I[tid][0] + 1;
  attr(tid, 0, val0, 1);
  setHin(tid, 0);
  pc[tid][0] = 6;
}

void _0_4(int tid)
{
  __VERIFIER_assume((Lvalue[tid][1] != tid) && (Lvalue[tid][1] != (-128)));
  __VERIFIER_assume(I[tid][0] < (10 - 1));
  TYPEOFVALUES val0 = I[tid][0] + 1;
  attr(tid, 0, val0, 1);
  setHin(tid, 1);
  pc[tid][0] = 6;
}

void _0_5(int tid)
{
  __VERIFIER_assume((Lvalue[tid][1] != tid) && (Lvalue[tid][1] != (-128)));
  __VERIFIER_assume(I[tid][0] == (10 - 1));
  TYPEOFVALUES val0 = I[tid][0] - 1;
  attr(tid, 0, val0, 1);
  setHin(tid, 1);
  pc[tid][0] = 6;
}

void _0_6(int tid)
{
  TYPEOFVALUES val0 = tid;
  TYPEOFVALUES val1 = tid;
  lstig(tid, 0, val0, 1);
  lstig(tid, 1, val1, 0);
  TYPEOFPC pc0 = __VERIFIER_nondet_int();
  __VERIFIER_assume((((pc0 == 2) || (pc0 == 3)) || (pc0 == 4)) || (pc0 == 5));
  pc[tid][0] = pc0;
}

int main(void)
{
  init();
  TYPEOFAGENTID firstAgent = 0;
  while (1)
  {
    if ((_Bool) __VERIFIER_nondet_int())
    {
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

        default:
        {
        }

      }

      if (firstAgent == (3 - 1))
      {
        firstAgent = 0;
      }
      else
      {
        firstAgent++;
      }

    }
    else
    {
      _Bool propagate_or_confirm = __VERIFIER_nondet_int();
      if (propagate_or_confirm)
        propagate();
      else
        confirm();

    }

    if (((((((0 == 1) || (__abs(I[0][0] - I[1][0]) >= 2)) && ((0 == 2) || (__abs(I[0][0] - I[2][0]) >= 2))) && ((1 == 0) || (__abs(I[1][0] - I[0][0]) >= 2))) && ((1 == 2) || (__abs(I[1][0] - I[2][0]) >= 2))) && ((2 == 0) || (__abs(I[2][0] - I[0][0]) >= 2))) && ((2 == 1) || (__abs(I[2][0] - I[1][0]) >= 2)))
    {
      return 0;
    }

  }

}


