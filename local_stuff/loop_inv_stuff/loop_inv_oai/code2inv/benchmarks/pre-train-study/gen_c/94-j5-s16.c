int main()
{
  int i;
  int j;
  int k;
  int n;
  int junk_0 = 6;
  int junk_1 = 4;
  int junk_2 = 2;
  int junk_3 = 8;
  int junk_4 = 5;
  //skip 
  assume ((k) >= (0));
  assume ((n) >= (0));
  i = 0;
  
  j = 0;
  
  while(((i) <= (n)))
  {
    //tb 
    i = ((i) + (1));
    junk_1 = 614;
    j = ((j) + (i));
    junk_4 = junk_3;
  }
    //fb 
  assert ((((i) + (((j) + (k))))) > (((2) * (n))));
  //skip 


}
