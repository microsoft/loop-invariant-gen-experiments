int main()
{
  int i;
  int j;
  int k;
  int n;
  int junk_0 = 8;
  int junk_1 = 8;
  int junk_2 = 5;
  int junk_3 = 5;
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
    junk_4 = 142;
    j = ((j) + (i));
    junk_1 = 16;
  }
    //fb 
  assert ((((i) + (((j) + (k))))) > (((2) * (n))));
  //skip 


}
