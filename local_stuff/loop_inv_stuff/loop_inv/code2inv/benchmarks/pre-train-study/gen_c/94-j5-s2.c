int main()
{
  int i;
  int j;
  int k;
  int n;
  int junk_0 = 0;
  int junk_1 = 1;
  int junk_2 = 0;
  int junk_3 = 3;
  int junk_4 = 2;
  //skip 
  assume ((k) >= (0));
  assume ((n) >= (0));
  i = 0;
  
  j = 0;
  
  while(((i) <= (n)))
  {
    //tb 
    i = ((i) + (1));
    junk_2 = junk_3;
    j = ((j) + (i));
    junk_4 = 108 - (junk_2);
  }
    //fb 
  assert ((((i) + (((j) + (k))))) > (((2) * (n))));
  //skip 


}
