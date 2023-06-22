int main()
{
   int a[5];
   int len = 0;
   bool c = unknown();
   int i;
   while (c)
   {
      if (len == 4)
         len = 0;

      a[len] = 0;

      len++;
   }
   assert(len == 5);
}
