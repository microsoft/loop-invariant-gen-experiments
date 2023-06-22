int main()
{
  int x = 0;
  int y = 0;
  int N;
 
  if (N < 0)
    return;
 
  while (true)
  {
    if (x <= N)
      y++;
    else if (x >= N + 1)
      y--;
    else
      return;

    if (y < 0)
      break;
    x++;
  }
 
  assert(!((N >= 0) && (y == -1) && (x >= 2 * N + 3)));
}
