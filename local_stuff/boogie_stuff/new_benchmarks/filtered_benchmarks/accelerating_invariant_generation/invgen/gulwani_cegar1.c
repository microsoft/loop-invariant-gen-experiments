
int main()
{
  int x, y;
  assume(0 <= x);
  assume(x <= 2);
  assume(0 <= y);
  assume(y <= 2);
  while (unknown())
  {
    x += 2;
    y += 2;
  }
  if (y >= 0 && y <= 0 && 4 <= x)
  {
    assert(x < 4);
  }
}
