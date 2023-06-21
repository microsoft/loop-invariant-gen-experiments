int main()
{
  int x = unknown_int();
  int y = unknown_int();
  int z = unknown_int();
  assume(x < 100);
  assume(z < 100);
  while (x < 100 && 100 < z)
  {
    bool tmp = unknown();
    if (tmp)
    {
      x++;
    }
    else
    {
      x--;
      z--;
    }
  }

  assert(x >= 100 || z <= 100);
}
