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


TYPEOFVALUES I_0_0;
TYPEOFVALUES I_1_0;
TYPEOFVALUES I_2_0;
TYPEOFVALUES getI(TYPEOFAGENTID i, int j)
{
  switch (i)
  {
    case 0:
      return I_0_0;

    case 1:
      return I_1_0;

    case 2:
      return I_2_0;

    default:
    {
    }

  }

}

TYPEOFPC pc_0_0;
TYPEOFPC pc_1_0;
TYPEOFPC pc_2_0;
TYPEOFVALUES getpc(TYPEOFAGENTID i, int j)
{
  switch (i)
  {
    case 0:
      return pc_0_0;

    case 1:
      return pc_1_0;

    case 2:
      return pc_2_0;

    default:
    {
    }

  }

}

void setpc(TYPEOFAGENTID i, int j, TYPEOFPC value)
{
  switch (i)
  {
    case 0:
      pc_0_0 = value;
      break;

    case 1:
      pc_1_0 = value;
      break;

    case 2:
      pc_2_0 = value;
      break;

    default:
    {
    }

  }

}

TYPEOFTIME __LABS_time;
const TYPEOFKEYLID tupleStart_0 = 0;
const TYPEOFKEYLID tupleStart_1 = 1;
const TYPEOFKEYLID tupleEnd_0 = 0;
const TYPEOFKEYLID tupleEnd_1 = 1;
_Bool Hin_0_0;
_Bool Hin_0_1;
_Bool Hin_1_0;
_Bool Hin_1_1;
_Bool Hin_2_0;
_Bool Hin_2_1;
TYPEOFVALUES getHin(int i, int j)
{
  switch (i)
  {
    case 0:
      return (j == 0) ? (Hin_0_0) : (Hin_0_1);

    case 1:
      return (j == 0) ? (Hin_1_0) : (Hin_1_1);

    case 2:
      return (j == 0) ? (Hin_2_0) : (Hin_2_1);

    default:
    {
    }

  }

}

_Bool Hout_0_0;
_Bool Hout_0_1;
_Bool Hout_1_0;
_Bool Hout_1_1;
_Bool Hout_2_0;
_Bool Hout_2_1;
TYPEOFVALUES getHout(int i, int j)
{
  switch (i)
  {
    case 0:
      return (j == 0) ? (Hout_0_0) : (Hout_0_1);

    case 1:
      return (j == 0) ? (Hout_1_0) : (Hout_1_1);

    case 2:
      return (j == 0) ? (Hout_2_0) : (Hout_2_1);

    default:
    {
    }

  }

}

unsigned char HinCnt_0;
unsigned char HinCnt_1;
unsigned char HinCnt_2;
unsigned char HoutCnt_0;
unsigned char HoutCnt_1;
unsigned char HoutCnt_2;
TYPEOFVALUES getHinCnt(int i)
{
  switch (i)
  {
    case 0:
      return HinCnt_0;

    case 1:
      return HinCnt_1;

    case 2:
      return HinCnt_2;

    default:
    {
    }

  }

}

void setHinCnt(int i, unsigned char value)
{
  switch (i)
  {
    case 0:
      HinCnt_0 = value;
      break;

    case 1:
      HinCnt_1 = value;
      break;

    case 2:
      HinCnt_2 = value;
      break;

    default:
    {
    }

  }

}

unsigned char getHoutCnt(int i)
{
  switch (i)
  {
    case 0:
      return HoutCnt_0;

    case 1:
      return HoutCnt_1;

    case 2:
      return HoutCnt_2;

    default:
    {
    }

  }

}

void setHoutCnt(int i, unsigned char value)
{
  switch (i)
  {
    case 0:
      HoutCnt_0 = value;
      break;

    case 1:
      HoutCnt_1 = value;
      break;

    case 2:
      HoutCnt_2 = value;
      break;

    default:
    {
    }

  }

}

void setHin(TYPEOFAGENTID id, TYPEOFKEYLID key)
{
  if (key == 0)
    setHinCnt(id, getHinCnt(id) + (!getHin(id, tupleStart_0)));
  else
    setHinCnt(id, getHinCnt(id) + (!getHin(id, tupleStart_1)));

  switch (id)
  {
    case 0:
      switch (key)
    {
      case 0:
        Hin_0_0 = 1;
        break;

      case 1:
        Hin_0_1 = 1;
        break;

    }

      break;

    case 1:
      switch (key)
    {
      case 0:
        Hin_1_0 = 1;
        break;

      case 1:
        Hin_1_1 = 1;
        break;

    }

      break;

    case 2:
      switch (key)
    {
      case 0:
        Hin_2_0 = 1;
        break;

      case 1:
        Hin_2_1 = 1;
        break;

    }

      break;

    default:
    {
    }

  }

}

void clearHin(TYPEOFAGENTID id, TYPEOFKEYLID key)
{
  if (key == 0)
    setHinCnt(id, getHinCnt(id) - getHin(id, tupleStart_0));
  else
    setHinCnt(id, getHinCnt(id) - getHin(id, tupleStart_1));

  switch (id)
  {
    case 0:
      switch (key)
    {
      case 0:
        Hin_0_0 = 0;
        break;

      case 1:
        Hin_0_1 = 0;
        break;

    }

      break;

    case 1:
      switch (key)
    {
      case 0:
        Hin_1_0 = 0;
        break;

      case 1:
        Hin_1_1 = 0;
        break;

    }

      break;

    case 2:
      switch (key)
    {
      case 0:
        Hin_2_0 = 0;
        break;

      case 1:
        Hin_2_1 = 0;
        break;

    }

      break;

    default:
    {
    }

  }

}

void setHout(TYPEOFAGENTID id, TYPEOFKEYLID key)
{
  if (key == 0)
    setHoutCnt(id, getHoutCnt(id) + (!getHout(id, tupleStart_0)));
  else
    setHoutCnt(id, getHoutCnt(id) + (!getHout(id, tupleStart_1)));

  switch (id)
  {
    case 0:
      switch (key)
    {
      case 0:
        Hout_0_0 = 1;
        break;

      case 1:
        Hout_0_1 = 1;
        break;

    }

      break;

    case 1:
      switch (key)
    {
      case 0:
        Hout_1_0 = 1;
        break;

      case 1:
        Hout_1_1 = 1;
        break;

    }

      break;

    case 2:
      switch (key)
    {
      case 0:
        Hout_2_0 = 1;
        break;

      case 1:
        Hout_2_1 = 1;
        break;

    }

      break;

    default:
    {
    }

  }

}

void clearHout(TYPEOFAGENTID id, TYPEOFKEYLID key)
{
  if (key == 0)
    setHoutCnt(id, getHoutCnt(id) - getHout(id, tupleStart_0));
  else
    setHoutCnt(id, getHoutCnt(id) - getHout(id, tupleStart_1));

  switch (id)
  {
    case 0:
      switch (key)
    {
      case 0:
        Hout_0_0 = 0;
        break;

      case 1:
        Hout_0_1 = 0;
        break;

    }

      break;

    case 1:
      switch (key)
    {
      case 0:
        Hout_1_0 = 0;
        break;

      case 1:
        Hout_1_1 = 0;
        break;

    }

      break;

    case 2:
      switch (key)
    {
      case 0:
        Hout_2_0 = 0;
        break;

      case 1:
        Hout_2_1 = 0;
        break;

    }

      break;

    default:
    {
    }

  }

}

TYPEOFTIME now(void)
{
  return ++__LABS_time;
}

TYPEOFVALUES Lvalue_0_0;
TYPEOFVALUES Lvalue_0_1;
TYPEOFVALUES Lvalue_1_0;
TYPEOFVALUES Lvalue_1_1;
TYPEOFVALUES Lvalue_2_0;
TYPEOFVALUES Lvalue_2_1;
TYPEOFVALUES Ltstamp_0_0;
TYPEOFVALUES Ltstamp_0_1;
TYPEOFVALUES Ltstamp_1_0;
TYPEOFVALUES Ltstamp_1_1;
TYPEOFVALUES Ltstamp_2_0;
TYPEOFVALUES Ltstamp_2_1;
TYPEOFVALUES getLvalue(int i, int j)
{
  switch (i)
  {
    case 0:
      return (j == 0) ? (Lvalue_0_0) : (Lvalue_0_1);

    case 1:
      return (j == 0) ? (Lvalue_1_0) : (Lvalue_1_1);

    case 2:
      return (j == 0) ? (Lvalue_2_0) : (Lvalue_2_1);

    default:
    {
    }

  }

}

void setLvalue(TYPEOFAGENTID id, TYPEOFKEYLID key, TYPEOFVALUES value)
{
  switch (id)
  {
    case 0:
      if (key == 0)
    {
      Lvalue_0_0 = value;
    }
    else
    {
      Lvalue_0_1 = value;
    }

      break;

    case 1:
      if (key == 0)
    {
      Lvalue_1_0 = value;
    }
    else
    {
      Lvalue_1_1 = value;
    }

      break;

    case 2:
      if (key == 0)
    {
      Lvalue_2_0 = value;
    }
    else
    {
      Lvalue_2_1 = value;
    }

      break;

    default:
    {
    }

  }

}

TYPEOFTIME getLtstamp(int i, int j)
{
  switch (i)
  {
    case 0:
      return (j == 0) ? (Ltstamp_0_0) : (Ltstamp_0_1);

    case 1:
      return (j == 0) ? (Ltstamp_1_0) : (Ltstamp_1_1);

    case 2:
      return (j == 0) ? (Ltstamp_2_0) : (Ltstamp_2_1);

    default:
    {
    }

  }

}

void setLtstamp(TYPEOFAGENTID id, TYPEOFKEYLID key, TYPEOFVALUES value)
{
  switch (id)
  {
    case 0:
      if (key == 0)
    {
      Ltstamp_0_0 = value;
    }
    else
    {
      Ltstamp_0_1 = value;
    }

      break;

    case 1:
      if (key == 0)
    {
      Ltstamp_1_0 = value;
    }
    else
    {
      Ltstamp_1_1 = value;
    }

      break;

    case 2:
      if (key == 0)
    {
      Ltstamp_2_0 = value;
    }
    else
    {
      Ltstamp_2_1 = value;
    }

      break;

    default:
    {
    }

  }

}

TYPEOFTIME timeof(TYPEOFAGENTID id, TYPEOFKEYLID key)
{
  return getLtstamp(id, key);
}

TYPEOFKEYLID getTupleStart(int i)
{
  return (i == 0) ? (tupleStart_0) : (tupleStart_1);
}

TYPEOFKEYLID getTupleEnd(int i)
{
  return (i == 0) ? (tupleEnd_0) : (tupleEnd_1);
}

_Bool link(TYPEOFAGENTID __LABS_link1, TYPEOFAGENTID __LABS_link2, TYPEOFKEYLID key)
{
  _Bool __LABS_link = 0;
  if ((key >= 0) && (key <= 0))
  {
    __LABS_link = ((getI(__LABS_link1, 0) - getI(__LABS_link2, 0)) >= 0) && ((getI(__LABS_link1, 0) - getI(__LABS_link2, 0)) <= 2);
  }
  else
    if ((key >= 1) && (key <= 1))
  {
    __LABS_link = ((getI(__LABS_link2, 0) - getI(__LABS_link1, 0)) > 0) && ((getI(__LABS_link2, 0) - getI(__LABS_link1, 0)) <= 2);
  }


  return __LABS_link;
}

void attr(TYPEOFAGENTID id, TYPEOFKEYIID key, TYPEOFVALUES value, _Bool check)
{
  __VERIFIER_assume((!check) || (getHoutCnt(id) == 0));
  __VERIFIER_assume((!check) || (getHinCnt(id) == 0));
  switch (id)
  {
    case 0:
      I_0_0 = value;
      break;

    case 1:
      I_1_0 = value;
      break;

    case 2:
      I_2_0 = value;
      break;

  }

  now();
}

void lstig(TYPEOFAGENTID id, TYPEOFKEYLID key, TYPEOFVALUES value, _Bool check)
{
  __VERIFIER_assume((!check) || (getHoutCnt(id) == 0));
  __VERIFIER_assume((!check) || (getHinCnt(id) == 0));
  setLvalue(id, key, value);
  if (key == 0)
    setLtstamp(id, tupleStart_0, now());
  else
    setLtstamp(id, tupleStart_1, now());

  setHout(id, key);
}

_Bool differentLstig(TYPEOFAGENTID comp1, TYPEOFAGENTID comp2, TYPEOFKEYLID key)
{
  TYPEOFKEYLID k = (key == 0) ? (tupleStart_0) : (tupleStart_1);
  return (getLvalue(comp1, k) != getLvalue(comp1, k)) || (getLtstamp(comp1, k) != getLtstamp(comp2, k));
}

void confirm(void)
{
  TYPEOFAGENTID guessedcomp = __VERIFIER_nondet_int();
  __VERIFIER_assume(guessedcomp < 3);
  __VERIFIER_assume(getHinCnt(guessedcomp) > 0);
  TYPEOFKEYLID guessedkey = __VERIFIER_nondet_int();
  __VERIFIER_assume(guessedkey < 2);
  __VERIFIER_assume(getHin(guessedcomp, guessedkey) == 1);
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
          if (next <= getTupleEnd(guessedkey))
            setLvalue(i, next, getLvalue(guessedcomp, next));

        }

        setLtstamp(i, guessedkey, t);
      }

    }

  }

  clearHin(guessedcomp, guessedkey);
}

void propagate(void)
{
  TYPEOFAGENTID guessedcomp = __VERIFIER_nondet_int();
  __VERIFIER_assume(guessedcomp < 3);
  __VERIFIER_assume(getHoutCnt(guessedcomp) > 0);
  TYPEOFKEYLID guessedkey = __VERIFIER_nondet_int();
  __VERIFIER_assume(guessedkey < 2);
  __VERIFIER_assume(getHout(guessedcomp, guessedkey) == 1);
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
        if (next <= getTupleEnd(guessedkey))
          setLvalue(i, next, getLvalue(guessedcomp, next));

      }

      setLtstamp(i, guessedkey, t);
    }

  }

  clearHout(guessedcomp, guessedkey);
}

void init()
{
  Ltstamp_0_0 = 0;
  Ltstamp_0_1 = 0;
  Ltstamp_1_0 = 0;
  Ltstamp_1_1 = 0;
  Ltstamp_2_0 = 0;
  Ltstamp_2_1 = 0;
  Hin_0_0 = 0;
  Hin_0_1 = 0;
  Hin_1_0 = 0;
  Hin_1_1 = 0;
  Hin_2_0 = 0;
  Hin_2_1 = 0;
  Hout_0_0 = 0;
  Hout_0_1 = 0;
  Hout_1_0 = 0;
  Hout_1_1 = 0;
  Hout_2_0 = 0;
  Hout_2_1 = 0;
  HinCnt_0 = 0;
  HinCnt_1 = 0;
  HinCnt_2 = 0;
  HoutCnt_0 = 0;
  HoutCnt_1 = 0;
  HoutCnt_2 = 0;
  pc_0_0 = 6;
  pc_1_0 = 6;
  pc_2_0 = 6;
  Lvalue_0_0 = -128;
  Lvalue_1_0 = -128;
  Lvalue_2_0 = -128;
  Lvalue_0_1 = -128;
  Lvalue_1_1 = -128;
  Lvalue_2_1 = -128;
  int i00 = __VERIFIER_nondet_int();
  __VERIFIER_assume((i00 >= 1) && (i00 < 10));
  I_0_0 = i00;
  int i10 = __VERIFIER_nondet_int();
  __VERIFIER_assume((i10 >= 1) && (i10 < 10));
  I_1_0 = i10;
  int i20 = __VERIFIER_nondet_int();
  __VERIFIER_assume((i20 >= 1) && (i20 < 10));
  I_2_0 = i20;
  Ltstamp_0_0 = now();
  Ltstamp_0_1 = now();
  Ltstamp_1_0 = now();
  Ltstamp_1_1 = now();
  Ltstamp_2_0 = now();
  Ltstamp_2_1 = now();
  now();
}

void _0_2(int tid)
{
  __VERIFIER_assume((getLvalue(tid, 0) != tid) && (getLvalue(tid, 0) != (-128)));
  __VERIFIER_assume(getI(tid, 0) > 0);
  TYPEOFVALUES val0 = getI(tid, 0) - 1;
  attr(tid, 0, val0, 1);
  setHin(tid, 0);
  setpc(tid, 0, 6);
}

void _0_3(int tid)
{
  __VERIFIER_assume((getLvalue(tid, 0) != tid) && (getLvalue(tid, 0) != (-128)));
  __VERIFIER_assume(getI(tid, 0) == 0);
  TYPEOFVALUES val0 = getI(tid, 0) + 1;
  attr(tid, 0, val0, 1);
  setHin(tid, 0);
  setpc(tid, 0, 6);
}

void _0_4(int tid)
{
  __VERIFIER_assume((getLvalue(tid, 1) != tid) && (getLvalue(tid, 1) != (-128)));
  __VERIFIER_assume(getI(tid, 0) < (10 - 1));
  TYPEOFVALUES val0 = getI(tid, 0) + 1;
  attr(tid, 0, val0, 1);
  setHin(tid, 1);
  setpc(tid, 0, 6);
}

void _0_5(int tid)
{
  __VERIFIER_assume((getLvalue(tid, 1) != tid) && (getLvalue(tid, 1) != (-128)));
  __VERIFIER_assume(getI(tid, 0) == (10 - 1));
  TYPEOFVALUES val0 = getI(tid, 0) - 1;
  attr(tid, 0, val0, 1);
  setHin(tid, 1);
  setpc(tid, 0, 6);
}

void _0_6(int tid)
{
  TYPEOFVALUES val0 = tid;
  TYPEOFVALUES val1 = tid;
  lstig(tid, 0, val0, 1);
  lstig(tid, 1, val1, 0);
  TYPEOFPC pc0 = __VERIFIER_nondet_int();
  __VERIFIER_assume((((pc0 == 2) || (pc0 == 3)) || (pc0 == 4)) || (pc0 == 5));
  setpc(tid, 0, pc0);
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

    if (((((((0 == 1) || (__abs(getI(0, 0) - getI(1, 0)) >= 2)) && ((0 == 2) || (__abs(getI(0, 0) - getI(2, 0)) >= 2))) && ((1 == 0) || (__abs(getI(1, 0) - getI(0, 0)) >= 2))) && ((1 == 2) || (__abs(getI(1, 0) - getI(2, 0)) >= 2))) && ((2 == 0) || (__abs(getI(2, 0) - getI(0, 0)) >= 2))) && ((2 == 1) || (__abs(getI(2, 0) - getI(1, 0)) >= 2)))
    {
      return 0;
    }

  }

}


