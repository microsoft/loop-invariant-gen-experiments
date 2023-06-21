int main()
{
  int outfilelen;
  int nchar = 0;
  int out = 0;

  if (!(outfilelen > 0))
  {
    return;
  }
  while (unknown())
  {
    if (unknown())
    {
      if (unknown())
      {
        break;
      }

      if (unknown())
      {
        out = 0;
        nchar = 0;
        continue;
      }
      else
      {
        if (unknown())
        {
          break;
        }

        nchar++;
        if (nchar >= outfilelen)
        {
          break;
        }

        assert(0 <= out);
        assert(out < outfilelen);
        out++;
      }
    }
    else
    {
      nchar++;
      if (nchar >= outfilelen)
        break;

      assert(0 <= out);
      assert(out < outfilelen);
      out++;
      if (unknown())
        break;
    }
  }
  assert(0 <= out); // 5
  assert(out < outfilelen);
  out++;
}
