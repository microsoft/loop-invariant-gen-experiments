int main()
{
  int i;
  int j;
  int k;
  int n;
  int junk_0 = 7;
  int junk_1 = 5;
  int junk_2 = 2;
  int junk_3 = 2;
  int junk_4 = 8;
  //skip 
  assume ((k) >= (0));
  assume ((n) >= (0));
  i = 0;
  
  j = 0;
  
  while(((i) <= (n)))
  {
    //tb 
    i = ((i) + (1));
    junk_1 = junk_4;
    j = ((j) + (i));
    junk_4 = junk_0;
  }
    //fb 
  assert ((((i) + (((j) + (k))))) > (((2) * (n))));
  //skip 


}
