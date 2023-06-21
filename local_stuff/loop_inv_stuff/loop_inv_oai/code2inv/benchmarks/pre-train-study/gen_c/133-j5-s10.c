int main()
{
  int n;
  int x;
  int junk_0 = 8;
  int junk_1 = 2;
  int junk_2 = 8;
  int junk_3 = 8;
  int junk_4 = 1;
  //skip 
  x = 0;
  
  assume ((n) >= (0));
  while(((x) < (n)))
  {
    //tb 
    x = ((x) + (1));
    junk_2 = junk_3 - (junk_4);
  }
    //fb 
  assert ((x) == (n));
  //skip 


}
