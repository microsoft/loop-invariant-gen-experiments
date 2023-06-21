int main()
{
  int i;
  int j;
  int k;
  int n;
  int junk_0 = 3;
  int junk_1 = 3;
  int junk_2 = 4;
  int junk_3 = 5;
  int junk_4 = 1;
  //skip 
  assume ((k) >= (0));
  assume ((n) >= (0));
  i = 0;
  
  j = 0;
  
  while(((i) <= (n)))
  {
    //tb 
    i = ((i) + (1));
    junk_3 = 218;
    j = ((j) + (i));
    junk_0 = junk_1;
  }
    //fb 
  assert ((((i) + (((j) + (k))))) > (((2) * (n))));
  //skip 


}
