int main()
{
  int N_LIN = unknown_int();
  assume(N_LIN >= 0);
  int N_COL = unknown_int();
  assume(N_COL >= 0);
  int j, k;
  int matriz[N_COL][N_LIN];
  int maior;

  maior = unknown_int();
  j = 0;
  while (j < N_COL)
  {
    k = 0;
    while (k < N_LIN)
    {
      matriz[j][k] = unknown_int();

      if (matriz[j][k] > maior)
        maior = matriz[j][k];
      k++;
    }
    j++;
  }

  j = 0;
  while (j < N_COL)
  {
    k = 0;
    while (k < N_LIN)
    {
      assert(matriz[j][k] < maior);
      k++;
    }
    j++;
  }
}
