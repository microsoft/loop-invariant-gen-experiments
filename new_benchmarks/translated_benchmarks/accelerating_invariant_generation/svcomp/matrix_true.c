int main()
{
  int N_LIN = 1;
  int N_COL = 1;
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

      if (matriz[j][k] >= maior)
        maior = matriz[j][k];
      k++;
    }
    j++;
  }

  assert(matriz[0][0] <= maior);
}
