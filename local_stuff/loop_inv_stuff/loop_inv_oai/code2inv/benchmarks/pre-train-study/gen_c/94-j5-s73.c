int main()
{
  int i;
  int j;
  int k;
  int n;
  int junk_0 = 3;
  int junk_1 = 6;
  int junk_2 = 0;
  int junk_3 = 6;
  int junk_4 = 7;
  //skip 
  assume ((k) >= (0));
  assume ((n) >= (0));
  i = 0;
  
  j = 0;
  
  while(((i) <= (n)))
  {
    //tb 
    i = ((i) + (1));
    junk_3 = 696;
    j = ((j) + (i));
    junk_0 = junk_4 - (junk_3);
  }
    //fb 
  assert ((((i) + (((j) + (k))))) > (((2) * (n))));
  //skip 


}
