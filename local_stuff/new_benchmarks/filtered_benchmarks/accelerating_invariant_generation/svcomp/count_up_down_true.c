int main()
{
  int n = unknown_int(); // unsigned int
  assume(n >= 0);
  int x=n;
  int y=0; // unsigned int
  while(x>0)
  {
    x--;
    y++;
  }
  assert(y==n);
}

