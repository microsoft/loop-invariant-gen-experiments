int main()
{
  int INFINITY = 899;
  int nodecount = 5;
  int edgecount = 20;
  int source = 0;
  int Source[20] = {0, 4, 1, 1, 0, 0, 1, 3, 4, 4, 2, 2, 3, 0, 0, 3, 1, 2, 2, 3};
  int Dest[20] = {1, 3, 4, 1, 1, 4, 3, 4, 3, 0, 0, 0, 0, 2, 3, 0, 2, 1, 0, 4};
  int Weight[20] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19};
  int distance[5];
  int x, y;
  int i, j;

  i = 0;
  while (i < nodecount)
  {
    if (i == source)
    {
      distance[i] = 0;
    }
    else
    {
      distance[i] = INFINITY;
    }
    i++;
  }

  i = 0;
  while (i < nodecount)
  {
    j = 0;
    while (j < edgecount)
    {
      x = Dest[j];
      y = Source[j];
      if (distance[x] > distance[y] + Weight[j])
      {
        distance[x] = distance[y] + Weight[j];
      }
      j++;
    }
    i++;
  }

  i = 0;
  while (i < edgecount)
  {
    x = Dest[i];
    y = Source[i];
    if (distance[x] > distance[y] + Weight[i])
    {
      return;
    }
    i++;
  }

  i = 0;
  while (i < nodecount)
  {
    assert(distance[i] >= 0);
    i++;
  }
}