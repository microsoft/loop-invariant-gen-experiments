int main()
{
  int max = 5;
  int str1[max];
  int str2[max];
  int i, j;

  i = 0;
  while (i < max)
  {
    str1[i] = unknown_int();
    i++;
  }

  j = 0;

  i = max - 1;
  while (i >= 0)
  {
    str2[j] = str1[i];
    j++;
    i--;
  }

  j = max - 1;
  i = 0;
  while (i < max)
  {
    assert(str1[i] == str2[j]);
    j--;
    i++;
  }
}