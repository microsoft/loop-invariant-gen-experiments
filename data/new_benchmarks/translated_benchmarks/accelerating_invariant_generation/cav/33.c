int main()
{
  int k;
  int z = k;
  int x = 0;
  int y = 0;

  while (unknown())
  {
    int c = 0;
    while (unknown())
    {
      if (z == k + y - c)
      {
        x++;
        y++;
        c++;
      }
      else
      {
        x++;
        y--;
        c++;
      }
    }
    while (unknown())
    {
      x--;
      y--;
    }
    z = k + y;
  }
  assert(!(x <= y - 1 || x >= y + 1));
}
