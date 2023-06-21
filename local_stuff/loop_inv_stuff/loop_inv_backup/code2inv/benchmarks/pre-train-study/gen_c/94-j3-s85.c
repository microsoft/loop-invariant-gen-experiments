int main()
{
  int i;
  int j;
  int k;
  int n;
  int junk_0 = 0;
  int junk_1 = 7;
  int junk_2 = 6;
  //skip 
  assume ((k) >= (0));
  assume ((n) >= (0));
  i = 0;
  
  j = 0;
  
  while(((i) <= (n)))
  {
    //tb 
    i = ((i) + (1));
    junk_0 = 303;
    j = ((j) + (i));
    junk_1 = 166 + (junk_2);
  }
    //fb 
  assert ((((i) + (((j) + (k))))) > (((2) * (n))));
  //skip 


}
