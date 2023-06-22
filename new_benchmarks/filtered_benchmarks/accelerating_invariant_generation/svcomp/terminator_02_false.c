int main()
{
  int x = unknown_int();
  int y = unknown_int();
  int z = unknown_int();

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

  assert(false);
}
