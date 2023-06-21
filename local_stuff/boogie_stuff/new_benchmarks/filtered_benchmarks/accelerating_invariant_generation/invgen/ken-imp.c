int main()
{
  int i;
  int j;
  int x = i;
  int y = j;
  while (x != 0)
  {
    x--;
    y--;
  }
  if ((i == j) && (y != 0))
  {
    assert(false);
  }
}
