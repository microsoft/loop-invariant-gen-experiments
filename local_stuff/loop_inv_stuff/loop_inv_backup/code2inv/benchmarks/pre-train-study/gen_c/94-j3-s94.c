int main()
{
  int i;
  int j;
  int k;
  int n;
  int junk_0 = 9;
  int junk_1 = 5;
  int junk_2 = 1;
  //skip 
  assume ((k) >= (0));
  assume ((n) >= (0));
  i = 0;
  
  j = 0;
  
  while(((i) <= (n)))
  {
    //tb 
    i = ((i) + (1));
    junk_2 = junk_1 + (junk_1);
    j = ((j) + (i));
    junk_0 = 238 + (junk_2);
  }
    //fb 
  assert ((((i) + (((j) + (k))))) > (((2) * (n))));
  //skip 


}
