int main()
{
  int n;
  int x;
  int junk_0 = 8;
  int junk_1 = 6;
  int junk_2 = 6;
  int junk_3 = 8;
  int junk_4 = 2;
  //skip 
  x = 0;
  
  assume ((n) >= (0));
  while(((x) < (n)))
  {
    //tb 
    x = ((x) + (1));
    junk_0 = junk_2;
  }
    //fb 
  assert ((x) == (n));
  //skip 


}
