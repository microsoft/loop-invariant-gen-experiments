int main()
{
  int n;
  int x;
  int junk_0 = 0;
  int junk_1 = 6;
  int junk_2 = 4;
  int junk_3 = 6;
  int junk_4 = 4;
  //skip 
  x = 0;
  
  assume ((n) >= (0));
  while(((x) < (n)))
  {
    //tb 
    x = ((x) + (1));
    junk_2 = junk_0;
  }
    //fb 
  assert ((x) == (n));
  //skip 


}
