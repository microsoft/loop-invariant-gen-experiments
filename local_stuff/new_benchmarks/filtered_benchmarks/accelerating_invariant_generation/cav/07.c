int main()
{
  int n = unknown_int();
  int i = 0;
  int j = 0;
  if (!(n >= 0))
    return;
  while (i < n)
  {
    i++;
    j++;
  }
  assert(!(j >= n + 1));
}
