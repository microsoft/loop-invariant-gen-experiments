int main()
{
  int i;
  int j;
  int k;
  int n;
  int junk_0 = 7;
  int junk_1 = 9;
  int junk_2 = 3;
  //skip 
  assume ((k) >= (0));
  assume ((n) >= (0));
  i = 0;
  
  j = 0;
  
  while(((i) <= (n)))
  {
    //tb 
    i = ((i) + (1));
    junk_1 = junk_2;
    j = ((j) + (i));
    junk_2 = 204 + (junk_2);
  }
    //fb 
  assert ((((i) + (((j) + (k))))) > (((2) * (n))));
  //skip 


}
