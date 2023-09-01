int main()
{
  int i, j;
  i = 0;
  while (unknown())
  {
    i++;
  }
  if (i >= 100)
  {
  STUCK:
    goto STUCK;
  }
  j = 0;
  while (unknown())
  {
    i++;
    j++;
  }
  if (j >= 100)
  {
    goto STUCK;
  }
  assert(i < 200);
}
