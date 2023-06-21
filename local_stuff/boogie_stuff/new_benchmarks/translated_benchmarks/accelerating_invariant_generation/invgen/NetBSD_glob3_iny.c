int main()
{
  int buf_off, pattern_off, bound_off;

  int MAXPATHLEN;
  int error;
  int pathbuf_off;
  int pathend_off;
  int pathlim_off;

  if (!(MAXPATHLEN > 0))
  {
    return;
  }

  buf_off = 0;
  pattern_off = 0;

  bound_off = MAXPATHLEN;

  pathbuf_off = 0;
  pathend_off = 0;
  pathlim_off = MAXPATHLEN;

  error = 0;

  while (unknown())
  {
    int i;
    assert(0 <= pattern_off);
    assert(pattern_off <= MAXPATHLEN);
    if (unknown())
      continue;
    i = 0;
    while (true)
    {
      if (i > MAXPATHLEN)
      {
        return;
      }
      else
      {
        assert(0 <= i);
        assert(i <= MAXPATHLEN);
        i++;
        if (unknown())
        {
          return;
        }
      }
    }

    assert(0 <= pathlim_off);
    assert(pathlim_off <= MAXPATHLEN);

    if (i > MAXPATHLEN)
    {
      if (unknown())
      {
        if (unknown())
        {
          error = 5;
          return;
        }
        else
        {
          assert(0 <= i);
          assert(i <= MAXPATHLEN + 1);
          continue;
        }
      }
    }
    if (unknown())
    {
      assert(i <= MAXPATHLEN + 1);
      continue;
    }
  }
}
