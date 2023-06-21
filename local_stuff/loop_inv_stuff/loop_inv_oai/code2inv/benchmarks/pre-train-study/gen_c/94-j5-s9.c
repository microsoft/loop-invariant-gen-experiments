int main()
{
  int i;
  int j;
  int k;
  int n;
  int junk_0 = 7;
  int junk_1 = 8;
  int junk_2 = 4;
  int junk_3 = 9;
  int junk_4 = 0;
  //skip 
  assume ((k) >= (0));
  assume ((n) >= (0));
  i = 0;
  
  j = 0;
  
  while(((i) <= (n)))
  {
    //tb 
    i = ((i) + (1));
    junk_0 = junk_2;
    j = ((j) + (i));
    junk_3 = junk_2 + (464);
  }
    //fb 
  assert ((((i) + (((j) + (k))))) > (((2) * (n))));
  //skip 


}
