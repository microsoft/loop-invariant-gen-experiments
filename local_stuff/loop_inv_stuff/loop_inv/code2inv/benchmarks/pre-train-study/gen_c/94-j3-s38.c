int main()
{
  int i;
  int j;
  int k;
  int n;
  int junk_0 = 2;
  int junk_1 = 8;
  int junk_2 = 2;
  //skip 
  assume ((k) >= (0));
  assume ((n) >= (0));
  i = 0;
  
  j = 0;
  
  while(((i) <= (n)))
  {
    //tb 
    i = ((i) + (1));
    junk_2 = 55 - (junk_2);
    j = ((j) + (i));
    junk_2 = junk_0;
  }
    //fb 
  assert ((((i) + (((j) + (k))))) > (((2) * (n))));
  //skip 


}
