int main(void)
{
   int SIZE = 5;
   int n = SIZE;
   int array[SIZE];
   int i;

   i = SIZE - 1;
   while (i >= 0)
   {
      array[i] = i;
      i--;
   }

   int lh, rh, i, temp;

   lh = 0;
   while (lh < n)
   {
      rh = lh;
      i = lh + 1;
      while (i < n)
      {
         if (array[i] < array[rh])
         {
            rh = i;
         }
         i++;
      }
      temp = array[lh];
      array[lh] = array[rh];
      array[rh] = temp;
      lh++;
   }

   i = 0;
   while (i < SIZE)
   {
      assert(array[i] == i);
      i++;
   }
}
