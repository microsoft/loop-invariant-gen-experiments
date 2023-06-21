int main()
{
  int x = 0;
  int y = 0;
  while (unknown())
  {
    if (unknown())
    {
      x = x + 1;
      y = y + 100;
    }
    else if (unknown())
    {
      if (x >= 4)
      {
        x = x + 1;
        y = y + 1;
      }
    }
    /*else if (y > 10*w && z >= 100*x)
        {y = -y;}
      w = w+1; z = z+10;*/
    x = x; /* work around VC gen bug */
  }
  assert(!(x >= 4 && y <= 2));
}
