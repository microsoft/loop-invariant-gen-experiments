int main()
{
  int SIZE = unknown_int();
  assume(SIZE >= 0);
  int i, j, k, key;
  int v[SIZE];
  j = 1;
  while (j < SIZE)
  {
    key = v[j];
    i = j - 1;
    while ((i >= 0) && (v[i] > key))
    {
      if (i < 2)
        v[i + 1] = v[i];
      i = i - 1;
    }
    v[i + 1] = key;
    j++;
  }

  k = 1;
  while (k < SIZE)
  {
    assert(v[k - 1] <= v[k]);
    k++;
  }
}