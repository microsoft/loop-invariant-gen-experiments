int main()
{
  int x1 = unknown_int();
  int x2 = unknown_int();
  int x3 = unknown_int();
  assume(x1 >= 0);
  assume(x2 >= 0);
  assume(x3 >= 0);
  int d1 = 1;
  int d2 = 1;
  int d3 = 1;
  bool c1 = unknown();
  bool c2 = unknown();

  while (x1 > 0 && x2 > 0 && x3 > 0)
  {
    if (c1)
      x1 = x1 - d1;
    else if (c2)
      x2 = x2 - d2;
    else
      x3 = x3 - d3;
    c1 = unknown();
    c2 = unknown();
  }

  assert(x1 == 0 || x2 == 0 && x3 == 0);
}
