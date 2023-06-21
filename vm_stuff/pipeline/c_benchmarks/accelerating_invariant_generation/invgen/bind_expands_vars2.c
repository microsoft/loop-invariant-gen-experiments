int main()
{
  int cp1_off, n1, n2, mc_i;
  int MAXDATA;
  if (!(MAXDATA > 0))
  {
    return;
  }

  if (!(n1 <= MAXDATA * 2))
  {
    return;
  }

  if (!(cp1_off <= n1))
  {
    return;
  }

  if (!(n2 <= MAXDATA * 2 - n1))
  {
    return;
  }

  mc_i = 0;
  while (mc_i < n2)
  {
    assert(cp1_off + mc_i < MAXDATA * 2);
    mc_i++;
  }
}
