int main()
{
  int x = 0;
  int y = 0;

  while (unknown())
  {
    x += 1;
    y += 1;
  }

  while (x > 0)
  {
    x = x - 1;
    y = y - 1;
  }

  assert(!(y <= -1));
}