int main()
{
  int fbuflen;
  int fb;

  if (!(fbuflen > 0))
  {
    return;
  }
  fb = 0;
  while (unknown())
  {
    if (unknown())
    {
      break;
    }
    if (unknown())
    {
      break;
    }

    assert(0 <= fb);
    assert(fb < fbuflen);
    fb++;
    if (fb >= fbuflen - 1)
    {
      fb = 0;
    }

    assert(0 <= fb);
    assert(fb < fbuflen);
    fb++;
    if (fb >= fbuflen - 1)
    {
      fb = 0;
    }

    assert(0 <= fb);
    assert(fb < fbuflen);

    fb++;
    if (fb >= fbuflen - 1)
    {
      fb = 0;
    }
  }
  if (fb > 0)
  {
    assert(0 <= fb);
    assert(fb < fbuflen);
  }
}
