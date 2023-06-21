int main()
{
  int MAX = unknown_int();
  assume(MAX > 0);
  int str1[MAX];
  int str2[MAX];
  int cont, i, j;
  cont = 0;

  i = 0;
  while (i < MAX)
  {
    str1[i] = unknown_int();
    i++;
  }

  j = 0;

  i = MAX - 1;
  while (i >= 0)
  {
    str2[j] = str1[0];
    j++;
    i--;
  }

  j = MAX - 1;
  i = 0;
  while (i < MAX)
  {
    assert(str1[i] == str2[j]);
    j--;
    i++;
  }
}