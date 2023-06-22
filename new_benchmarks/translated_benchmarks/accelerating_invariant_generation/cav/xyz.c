int main()
{
  int x, y, z;
  x = 0;
  y = 0;
  z = 0;

  while (unknown())
  {
    x++;
    y++;
    z -= 2;
  }

  while (x > 0)
  {
    z++;
    z++;
    x--;
    y--;
  }

  assert(!(z <= -1));
}
