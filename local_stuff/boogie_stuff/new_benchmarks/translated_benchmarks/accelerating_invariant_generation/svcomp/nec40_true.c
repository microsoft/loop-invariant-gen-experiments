void main()
{
  int x[100], y[100];
  int i, j, k;
  k = unknown_int();
  i = 0;
  while (x[i] != 0)
  {
    y[i] = x[i];
    i++;
  }
  y[i] = 0;

  assert(!((k >= 0 && k < i) && (y[k] != 0)));
}
