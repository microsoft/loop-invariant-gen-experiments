int main()
{
  int size = unknown_int();
  int item[size];
  int i;

  i = 0;
  while (i < size)
  {
    item[i] = i;
    i++;
  }

  i = 0;
  while (i < size)
  {
    int r = i + (unknown_int() % (size - i));
    int temp = item[i];
    item[i] = item[r];
    item[r] = temp;
    i++;
  }

  // bubblesort algo
  int a, b, t;

  a = 1;
  while (a < size)
  {
    b = size - 1;
    while (b >= a)
    {

      if (b - 1 < size && b < size)
      {
        if (item[b - 1] > item[b])
        {
          t = item[b - 1];
          item[b - 1] = item[b];
          item[b] = t;
        }
      }
      b--;
    }
    a++;
  }
}
