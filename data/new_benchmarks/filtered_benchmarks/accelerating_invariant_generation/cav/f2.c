int main()
{
  int x, y, z, w;
  x = 0;
  y = 0;
  z = 0;
  w = 0;

  while (unknown())
  {
    if (unknown())
    {
      x++;
      y = y + 2;
    }
    else if (unknown())
    {
      if (x >= 4)
      {
        x++;
        y = y + 3;
        z = z + 10;
        w = w + 10;
      }
    }
    else if (x >= z && w >= y + 1)
    {
      x = -x;
      y = -y;
    }
    x = x; /* this works around a VC gen bug */
  }
  assert(!(3 * x <= y - 1));
}
