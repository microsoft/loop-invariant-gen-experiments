int main()
{
  int x = 0;
  while (true)
  {
    while (true)
    {
      x = 1;
      break;
    }
    assert(x == 0);
  }

  assert(x == 0);
}
