int main()
{
  int scheme;
  int urilen, tokenlen;
  int cp, c;
  //  char *token[TOKEN_SZ];

  if (!(urilen > 0))
  {
    return;
  }
  if (!(tokenlen > 0))
  {
    return;
  }
  if (!(scheme >= 0))
  {
    return;
  }
  if (scheme == 0 || (urilen - 1 < scheme))
  {
    return;
  }

  cp = scheme;

  assert(cp - 1 < urilen);
  assert(0 <= cp - 1);

  if (unknown())
  {
    assert(cp < urilen);
    assert(0 <= cp);
    while (cp != urilen - 1)
    {
      if (unknown())
        break;
      assert(cp < urilen);
      assert(0 <= cp);
      ++cp;
    }
    assert(cp < urilen);
    assert(0 <= cp);
    if (cp == urilen - 1)
      return;
    assert(cp + 1 < urilen);
    assert(0 <= cp + 1);
    if (cp + 1 == urilen - 1)
      return;
    ++cp;

    scheme = cp;

    if (unknown())
    {
      c = 0;
      // token[0] = uri;
      assert(cp < urilen);
      assert(0 <= cp);
      while (cp != urilen - 1 && c < tokenlen - 1)
      {
        assert(cp < urilen);
        assert(0 <= cp);
        if (unknown())
        {
          ++c;
          /* OK */
          assert(c < tokenlen);
          assert(0 <= c);
          // token[c] = uri + cp + 1;
          assert(cp < urilen); // Interesting assert
          assert(0 <= cp);
          // uri[cp] = EOS;
        }
        ++cp;
      }
      return;
    }
  }
}
