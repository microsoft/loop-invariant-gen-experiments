int main()
{
  int tagbuf_len;
  int t;

  if (!(tagbuf_len >= 1))
    return;

  t = 0;

  --tagbuf_len;

  while (true)
  {
    if (t == tagbuf_len)
    {
      assert(0 <= t);
      assert(t <= tagbuf_len);
      return;
    }
    if (unknown())
    {
      break;
    }
    assert(0 <= t);
    assert(t <= tagbuf_len);
    t++;
  }

  assert(0 <= t);
  assert(t <= tagbuf_len);
  t++;
  while (true)
  {
    if (t == tagbuf_len)
    {
      assert(0 <= t);
      assert(t <= tagbuf_len);
      return;
    }

    if (unknown())
    {
      if (unknown())
      {
        assert(0 <= t);
        assert(t <= tagbuf_len);
        t++;
        if (t == tagbuf_len)
        {
          assert(0 <= t);
          assert(t <= tagbuf_len);
          return;
        }
      }
    }
    else if (unknown())
    {
      break;
    }

    assert(0 <= t);
    assert(t <= tagbuf_len);
    t++;
  }

  assert(0 <= t);
  assert(t <= tagbuf_len);
}