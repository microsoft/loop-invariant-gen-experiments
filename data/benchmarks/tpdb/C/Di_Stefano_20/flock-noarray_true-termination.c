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
typedef unsigned char TYPEOFTIME;
typedef unsigned char TYPEOFAGENTID;
typedef unsigned char TYPEOFKEYIID;
typedef unsigned char TYPEOFKEYLID;

TYPEOFVALUES mod(TYPEOFVALUES n, TYPEOFVALUES m)
{
  return (n >= 0) ? (n % m) : (m + (n % m));
}

TYPEOFVALUES I_0_0;
TYPEOFVALUES I_0_1;
TYPEOFVALUES I_1_0;
TYPEOFVALUES I_1_1;
TYPEOFVALUES I_2_0;
TYPEOFVALUES I_2_1;
TYPEOFVALUES getI(int i, int j)
{
  switch (i)
  {
    case 0:
      return (j == 0) ? (I_0_0) : (I_0_1);

    case 1:
      return (j == 0) ? (I_1_0) : (I_1_1);

    case 2:
      return (j == 0) ? (I_2_0) : (I_2_1);

    default:
    {
    }

  }

}

TYPEOFTIME __LABS_time;
unsigned char pc_0_0;
unsigned char pc_1_0;
unsigned char pc_2_0;
TYPEOFVALUES getpc(int i, int j)
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

void setpc(int i, int j, unsigned char value)
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

_Bool Hin_0_0;
_Bool Hin_1_0;
_Bool Hin_2_0;
TYPEOFVALUES getHin(int i, int j)
{
  switch (i)
  {
    case 0:
      return Hin_0_0;

    case 1:
      return Hin_1_0;

    case 2:
      return Hin_2_0;

    default:
    {
    }

  }

}

_Bool Hout_0_0;
_Bool Hout_1_0;
_Bool Hout_2_0;
TYPEOFVALUES getHout(int i, int j)
{
  switch (i)
  {
    case 0:
      return Hout_0_0;

    case 1:
      return Hout_1_0;

    case 2:
      return Hout_2_0;

    default:
    {
    }

  }

}

unsigned char HinCnt_0;
unsigned char HinCnt_1;
unsigned char HinCnt_2;
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

unsigned char HoutCnt_0;
unsigned char HoutCnt_1;
unsigned char HoutCnt_2;
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
TYPEOFVALUES Ltstamp_1_0;
TYPEOFVALUES Ltstamp_2_0;
const TYPEOFKEYLID tupleStart = 0;
const TYPEOFKEYLID tupleEnd = 1;
_Bool link(TYPEOFAGENTID __LABS_link1, TYPEOFAGENTID __LABS_link2, TYPEOFKEYLID key)
{
  //_Bool __LABS_link = 0;
  if ((key >= 0) && (key <= 1))
  {
    if ((((getI(__LABS_link1, 0) - getI(__LABS_link2, 0)) * (getI(__LABS_link1, 0) - getI(__LABS_link2, 0))) + ((getI(__LABS_link1, 1) - getI(__LABS_link2, 1)) * (getI(__LABS_link1, 1) - getI(__LABS_link2, 1)))) <= (5 * 5)) return 1;
  }

  return 0;
}

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
      return Ltstamp_0_0;

    case 1:
      return Ltstamp_1_0;

    case 2:
      return Ltstamp_2_0;

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
      Ltstamp_0_0 = value;
      break;

    case 1:
      Ltstamp_1_0 = value;
      break;

    case 2:
      Ltstamp_2_0 = value;
      break;

    default:
    {
    }

  }

}

TYPEOFTIME timeof(TYPEOFAGENTID id, TYPEOFKEYLID key)
{
  return getLtstamp(id, tupleStart);
}

void setHin(TYPEOFAGENTID id, TYPEOFKEYLID key)
{
  setHinCnt(id, getHinCnt(id) + (!getHin(id, tupleStart)));
  switch (id)
  {
    case 0:
      Hin_0_0 = 1;
      break;

    case 1:
      Hin_1_0 = 1;
      break;

    case 2:
      Hin_2_0 = 1;
      break;

    default:
    {
    }

  }

}

void clearHin(TYPEOFAGENTID id, TYPEOFKEYLID key)
{
  setHinCnt(id, getHinCnt(id) - getHin(id, tupleStart));
  switch (id)
  {
    case 0:
      Hin_0_0 = 0;
      break;

    case 1:
      Hin_1_0 = 0;
      break;

    case 2:
      Hin_2_0 = 0;
      break;

    default:
    {
    }

  }

}

void setHout(TYPEOFAGENTID id, TYPEOFKEYLID key)
{
  setHoutCnt(id, getHoutCnt(id) + (!getHout(id, tupleStart)));
  switch (id)
  {
    case 0:
      Hout_0_0 = 1;
      break;

    case 1:
      Hout_1_0 = 1;
      break;

    case 2:
      Hout_2_0 = 1;
      break;

    default:
    {
    }

  }

}

void clearHout(TYPEOFAGENTID id, TYPEOFKEYLID key)
{
  setHoutCnt(id, getHoutCnt(id) - getHout(id, tupleStart));
  switch (id)
  {
    case 0:
      Hout_0_0 = 0;
      break;

    case 1:
      Hout_1_0 = 0;
      break;

    case 2:
      Hout_2_0 = 0;
      break;

    default:
    {
    }

  }

}

void attr(TYPEOFAGENTID id, TYPEOFKEYIID key, TYPEOFVALUES value, _Bool check)
{
  __VERIFIER_assume((!check) || (getHoutCnt(id) == 0));
  __VERIFIER_assume((!check) || (getHinCnt(id) == 0));
  switch (id)
  {
    case 0:
      if (key == 0)
    {
      I_0_0 = value;
    }
    else
    {
      I_0_1 = value;
    }

      break;

    case 1:
      if (key == 0)
    {
      I_1_0 = value;
    }
    else
    {
      I_1_1 = value;
    }

      break;

    case 2:
      if (key == 0)
    {
      I_2_0 = value;
    }
    else
    {
      I_2_1 = value;
    }

      break;

    default:
    {
    }

  }

  now();
}

void lstig(TYPEOFAGENTID id, TYPEOFKEYLID key, TYPEOFVALUES value, _Bool check)
{
  __VERIFIER_assume((!check) || (getHoutCnt(id) == 0));
  __VERIFIER_assume((!check) || (getHinCnt(id) == 0));
  setLvalue(id, key, value);
  setHout(id, key);
}

void confirm(void)
{
  TYPEOFAGENTID guessedcomp = __VERIFIER_nondet_int();
  TYPEOFKEYLID guessedkey = __VERIFIER_nondet_int();
  TYPEOFAGENTID i = __VERIFIER_nondet_int();
  TYPEOFKEYLID k = __VERIFIER_nondet_int();
  TYPEOFKEYLID next = __VERIFIER_nondet_int();
  TYPEOFTIME t = __VERIFIER_nondet_int();
  __VERIFIER_assume(guessedcomp < 3);
  __VERIFIER_assume(getHinCnt(guessedcomp) > 0);
  __VERIFIER_assume(guessedkey < 2);
  __VERIFIER_assume(getHin(guessedcomp, guessedkey) == 1);
  t = timeof(guessedcomp, guessedkey);
  for (i = 0; i < 3; i++)
  {
    if (((guessedcomp != i) && (timeof(i, guessedkey) != t)) && link(guessedcomp, i, guessedkey))
    {
      setHout(i, guessedkey);
      if (timeof(i, guessedkey) < t)
      {
        clearHin(i, guessedkey);
        for (k = 0; k < 2; k++)
        {
          next = guessedkey + k;
          if (next <= tupleEnd)
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
  TYPEOFKEYLID guessedkey = __VERIFIER_nondet_int();
  TYPEOFAGENTID i = __VERIFIER_nondet_int();
  TYPEOFKEYLID k = __VERIFIER_nondet_int();
  TYPEOFKEYLID next = __VERIFIER_nondet_int();
  TYPEOFTIME t = __VERIFIER_nondet_int();
  __VERIFIER_assume(guessedcomp < 3);
  __VERIFIER_assume(getHoutCnt(guessedcomp) > 0);
  __VERIFIER_assume(guessedkey < 2);
  __VERIFIER_assume(getHout(guessedcomp, guessedkey) == 1);
  t = timeof(guessedcomp, guessedkey);
  for (i = 0; i < 3; i++)
  {
    if (((guessedcomp != i) && (timeof(i, guessedkey) < t)) && link(guessedcomp, i, guessedkey))
    {
      setHout(i, guessedkey);
      clearHin(i, guessedkey);
      for (k = 0; k < 2; k++)
      {
        next = guessedkey + k;
        if (next <= tupleEnd)
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
  Ltstamp_1_0 = 0;
  Ltstamp_2_0 = 0;
  Hin_0_0 = 0;
  Hin_1_0 = 0;
  Hin_2_0 = 0;
  Hout_0_0 = 0;
  Hout_1_0 = 0;
  Hout_2_0 = 0;
  HinCnt_0 = 0;
  HinCnt_1 = 0;
  HinCnt_2 = 0;
  HoutCnt_0 = 0;
  HoutCnt_1 = 0;
  HoutCnt_2 = 0;
  pc_0_0 = 2;
  pc_1_0 = 2;
  pc_2_0 = 2;
  I_0_0 = __VERIFIER_nondet_int();
  I_0_1 = __VERIFIER_nondet_int();
  I_1_0 = __VERIFIER_nondet_int();
  I_1_1 = __VERIFIER_nondet_int();
  I_2_0 = __VERIFIER_nondet_int();
  I_2_1 = __VERIFIER_nondet_int();
  Lvalue_0_0 = __VERIFIER_nondet_int();
  Lvalue_0_1 = __VERIFIER_nondet_int();
  Lvalue_1_0 = __VERIFIER_nondet_int();
  Lvalue_1_1 = __VERIFIER_nondet_int();
  Lvalue_2_0 = __VERIFIER_nondet_int();
  Lvalue_2_1 = __VERIFIER_nondet_int();
  __VERIFIER_assume((Lvalue_0_0 == (-1)) || (Lvalue_0_0 == 1));
  __VERIFIER_assume((Lvalue_1_0 == (-1)) || (Lvalue_1_0 == 1));
  __VERIFIER_assume((Lvalue_2_0 == (-1)) || (Lvalue_2_0 == 1));
  __VERIFIER_assume((Lvalue_0_1 == (-1)) || (Lvalue_0_1 == 1));
  __VERIFIER_assume((Lvalue_1_1 == (-1)) || (Lvalue_1_1 == 1));
  __VERIFIER_assume((Lvalue_2_1 == (-1)) || (Lvalue_2_1 == 1));
  __VERIFIER_assume((I_0_0 >= 0) && (I_0_0 < (5 - 0)));
  __VERIFIER_assume((I_1_0 >= 0) && (I_1_0 < (5 - 0)));
  __VERIFIER_assume((I_2_0 >= 0) && (I_2_0 < (5 - 0)));
  __VERIFIER_assume((I_0_1 >= 0) && (I_0_1 < (5 - 0)));
  __VERIFIER_assume((I_1_1 >= 0) && (I_1_1 < (5 - 0)));
  __VERIFIER_assume((I_2_1 >= 0) && (I_2_1 < (5 - 0)));
  Ltstamp_0_0 = now();
  Ltstamp_1_0 = now();
  Ltstamp_2_0 = now();
  now();
}

void _0_2(int tid)
{
  TYPEOFVALUES val0 = mod(getI(tid, 0) + getLvalue(tid, 0), 5);
  TYPEOFVALUES val1 = mod(getI(tid, 1) + getLvalue(tid, 1), 5);
  attr(tid, 0, val0, 1);
  attr(tid, 1, val1, 0);
  setHin(tid, 0);
  setHin(tid, 1);
  setpc(tid, 0, 2);
}

int main(void)
{
  TYPEOFAGENTID firstAgent = 0;
  init();
  while (1)
  {
    if ((_Bool) __VERIFIER_nondet_int())
    {
      switch (getpc(firstAgent, 0))
      {
        case 2:
          _0_2(firstAgent);
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

    if ((((((((((((Lvalue_0_0 == Lvalue_0_0) && (Lvalue_0_1 == Lvalue_0_1)) && (Lvalue_0_0 == Lvalue_1_0)) && (Lvalue_0_1 == Lvalue_1_1)) && (Lvalue_0_0 == Lvalue_2_0)) && (Lvalue_0_1 == Lvalue_2_1)) && (Lvalue_1_0 == Lvalue_1_0)) && (Lvalue_1_1 == Lvalue_1_1)) && (Lvalue_1_0 == Lvalue_2_0)) && (Lvalue_1_1 == Lvalue_2_1)) && (Lvalue_2_0 == Lvalue_2_0)) && (Lvalue_2_1 == Lvalue_2_1))
    {
      return 0;
    }

  }

}


