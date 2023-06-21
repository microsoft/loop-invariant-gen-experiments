int main()
{
  int i;
  int j;
  int k;
  int n;
  int junk_0 = 0;
  int junk_1 = 0;
  int junk_2 = 8;
  //skip 
  assume ((k) >= (0));
  assume ((n) >= (0));
  i = 0;
  
  j = 0;
  
  while(((i) <= (n)))
  {
    //tb 
    i = ((i) + (1));
    junk_2 = junk_2 + (junk_2);
    j = ((j) + (i));
    junk_2 = junk_1;
  }
    //fb 
  assert ((((i) + (((j) + (k))))) > (((2) * (n))));
  //skip 


}
