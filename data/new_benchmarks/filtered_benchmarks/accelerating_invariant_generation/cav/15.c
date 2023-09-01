int main()
{
  int n;
  int i, k, j;
  n = unknown_int();
  if (n < 1)
    return;
  if (k < n)
    return;
  j = 0;
  while (j <= n - 1)
  {
    j++;
    k--;
  }
  if (j < n)
    return;
  assert(!(k <= -1));
}
