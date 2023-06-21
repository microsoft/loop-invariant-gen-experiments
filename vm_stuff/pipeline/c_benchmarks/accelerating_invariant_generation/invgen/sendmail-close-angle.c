int main()
{
  int in;
  int inlen;
  int bufferlen;
  int buf;
  int buflim;

  if (!(bufferlen > 1))
  {
    return;
  }
  if (!(inlen > 0))
  {
    return;
  }
  if (!(bufferlen < inlen))
  {
    return;
  }
  buf = 0;
  in = 0;
  buflim = bufferlen - 2;
  while (unknown())
  {
    if (buf == buflim)
    {
      break;
    }
    assert(0 <= buf);
    assert(buf < bufferlen);
    buf++;
    in++;
    assert(0 <= in);
    assert(in < inlen);
  }

  assert(0 <= buf);
  assert(buf < bufferlen);
  buf++;

  assert(0 <= buf);
  assert(buf < bufferlen);
  buf++;
}
