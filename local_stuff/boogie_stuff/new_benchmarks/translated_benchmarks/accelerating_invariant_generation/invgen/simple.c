int main()
{
  int x = 0;
  int n;

  assume(n > 0);
  while (x < n)
  {
    x++;
  }
  assert(x <= n);
}
