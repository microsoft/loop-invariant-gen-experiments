int main()
{
  int x = 0;
  while (true)
  {
    while (true)
    {
      x = 0;
      break;
    }
    assert(x == 0);
  }
  assert(x != 0);
}
