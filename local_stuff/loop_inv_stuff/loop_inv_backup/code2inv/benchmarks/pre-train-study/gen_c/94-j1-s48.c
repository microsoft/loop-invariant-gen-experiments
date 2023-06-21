int main()
{
  int i;
  int j;
  int k;
  int n;
  int junk_0 = 8;
  //skip 
  assume ((k) >= (0));
  assume ((n) >= (0));
  i = 0;
  
  j = 0;
  
  while(((i) <= (n)))
  {
    //tb 
    i = ((i) + (1));
    junk_0 = junk_0;
    j = ((j) + (i));
    junk_0 = junk_0 - (junk_0);
  }
    //fb 
  assert ((((i) + (((j) + (k))))) > (((2) * (n))));
  //skip 


}
