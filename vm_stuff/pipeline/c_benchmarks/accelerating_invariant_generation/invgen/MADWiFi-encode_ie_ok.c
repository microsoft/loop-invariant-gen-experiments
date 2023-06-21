int main()
{
  int p;
  int i;
  int leader_len;
  int bufsize;
  int bufsize_0;
  int ielen;

  if (!(leader_len > 0))
  {
    return;
  }
  if (!(bufsize > 0))
  {
    return;
  }
  if (!(ielen > 0))
  {
    return;
  }

  if (bufsize < leader_len)
  {
    return;
  }

  p = 0;
  bufsize_0 = bufsize;
  bufsize -= leader_len;
  p += leader_len;

  if (bufsize < 2 * ielen)
  {
    return;
  }

  i = 0;
  while ((i < ielen) && (bufsize > 2))
  {
    assert(0 <= p);
    assert(p + 1 < bufsize_0);
    p += 2;
    i++;
  }
}
