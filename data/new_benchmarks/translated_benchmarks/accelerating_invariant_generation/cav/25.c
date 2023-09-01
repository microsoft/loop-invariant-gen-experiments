int main()
{
   int x = 0;
   int y = 0;
   int i = 0;
   int j = 0;
   while (unknown())
   {
      while (unknown())
      {
         if (x == y)
            i++;
         else
            j++;
      }
      if (i >= j)
      {
         x++;
         y++;
      }
      else
         y++;
   }
   assert(!(i <= j - 1));
}
