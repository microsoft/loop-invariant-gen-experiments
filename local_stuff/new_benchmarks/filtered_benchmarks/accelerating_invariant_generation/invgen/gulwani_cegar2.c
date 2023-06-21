int main()
{
  int x, m, n;
  x = 0;
  m = 0;
  while (x < n)
  {
    if (unknown())
      m = x;
    x++;
  }
  if (n > 0)
  {
    assert(0 <= m);
    assert(m < n);
  }
}
