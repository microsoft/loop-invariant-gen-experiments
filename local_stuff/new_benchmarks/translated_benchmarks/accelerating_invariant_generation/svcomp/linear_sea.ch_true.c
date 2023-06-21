int main()
{
  int SIZE = (unknown_int() / 8) + 1;
  assume(SIZE >= 0);
  int a[SIZE];
  a[SIZE / 2] = 3;
  
  int n = SIZE;
  int q = 3;
  int result;
  int j = 0;
  while (j < n && a[j] != q)
  {
    j++;
  }
  if (j < SIZE)
    result = 1;
  else
    result = 0;
  assert(result);
}